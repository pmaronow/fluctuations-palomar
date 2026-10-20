module
public import SKConstants.ScalarProcessLagVariableBlocks

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace SKConstants

lemma scalarLag_exp_drop (d : ℝ) (hd : 0≤d) (hd1 : d≤1) :
    d ≤ 8*(1-Real.exp (-d/4)) := by
  have he : Real.exp (-d/4)≤1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    linarith
  have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (d/4))
    (Real.exp_pos (-d/4)).le
  have hid : Real.exp (d/4)*Real.exp (-d/4)=1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hid] at hm
  have hy : 0≤1-Real.exp (-d/4) := by linarith
  have hn := mul_nonneg (by linarith : 0≤1-d/4) hy
  nlinarith

lemma scalarLag_growing_weight_max (δ t : ℝ) :
    (δ*Real.exp (t/4))*Real.exp (-t/4)=δ := by
  rw [mul_assoc, ← Real.exp_add]
  rw [show t/4 + -t/4 = 0 by ring, Real.exp_zero, mul_one]

lemma scalarLag_growing_weight_budget (δ : ℝ) (hδ : 0<δ) (t : ℕ → ℝ)
    (ht0 : t 0=0) (k : ℕ)
    (hstep : ∀ j<k, t (j+1)-t j=δ*Real.exp (t j/4))
    (hsmall : ∀ j<k, t (j+1)-t j≤1) :
    (∑ j ∈ Finset.range k, (t (j+1)-t j)^2*(Real.exp (-t j/4))^2)≤8*δ := by
  have hterm (j : ℕ) (hj : j<k) :
      (t (j+1)-t j)^2*(Real.exp (-t j/4))^2 ≤
        8*δ*(Real.exp (-t j/4)-Real.exp (-t (j+1)/4)) := by
    have hd : 0≤t (j+1)-t j := by rw [hstep j hj]; positivity
    have hdrop := mul_le_mul_of_nonneg_left
      (scalarLag_exp_drop _ hd (hsmall j hj)) (Real.exp_pos (-t j/4)).le
    have hexp : Real.exp (-t j/4)*Real.exp (-(t (j+1)-t j)/4)=
        Real.exp (-t (j+1)/4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hmax : (t (j+1)-t j)*Real.exp (-t j/4)=δ := by
      rw [hstep j hj]
      exact scalarLag_growing_weight_max δ (t j)
    have hdrop' : (t (j+1)-t j)*Real.exp (-t j/4) ≤
        8*(Real.exp (-t j/4)-Real.exp (-t (j+1)/4)) := by
      calc
        _ = Real.exp (-t j/4)*(t (j+1)-t j) := by ring
        _ ≤ _ := hdrop
        _ = _ := by rw [← hexp]; ring
    have hm := mul_le_mul_of_nonneg_left hdrop' hδ.le
    calc
      _ = δ*((t (j+1)-t j)*Real.exp (-t j/4)) := by rw [← hmax]; ring
      _ ≤ 8*δ*(Real.exp (-t j/4)-Real.exp (-t (j+1)/4)) := by nlinarith only [hm]
  calc
    _ ≤ ∑ j ∈ Finset.range k, 8*δ*(Real.exp (-t j/4)-Real.exp (-t (j+1)/4)) :=
      Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range.mp hj))
    _ = 8*δ*(1-Real.exp (-t k/4)) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub']
      simp [ht0]
    _ ≤ 8*δ := by have hp := Real.exp_pos (-t k/4); nlinarith

end SKConstants
