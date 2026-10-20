module

public import SKFluctuationsOAI.Probability.SKFluctuations.GaussianSmallScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

private theorem quadratic_nonneg_of_gram {a b c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hbc : b^2 ≤ a*c) (t : ℝ) :
    0 ≤ t^2*a - 2*t*b + c := by
  obtain rfl | ha := ha.eq_or_lt
  · have hb : b = 0 := by nlinarith [sq_nonneg b]
    simp only [hb, mul_zero, sub_zero, zero_add]
    exact hc
  · have hm : 0 ≤ a*(t^2*a - 2*t*b + c) := by
      nlinarith [sq_nonneg (t*a-b)]
    exact (mul_nonneg_iff_of_pos_left ha).mp hm

private theorem gram_of_quadratic_nonneg {a b c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ t^2*a - 2*t*b + c) : b^2 ≤ a*c := by
  obtain rfl | ha := ha.eq_or_lt
  · by_cases hb : b = 0
    · simp [hb]
    · have hh := h ((c+1)/(2*b))
      have he : ((c+1)/(2*b))^2*0 - 2*((c+1)/(2*b))*b+c = -1 := by
        field_simp
        <;> ring
      rw [he] at hh
      norm_num at hh
  · have hh := mul_nonneg ha.le (h (b/a))
    have he : a*((b/a)^2*a - 2*(b/a)*b+c) = a*c-b^2 := by
      field_simp
      <;> ring
    rw [he] at hh
    linarith

theorem actual_prefix_gram_sq_le {F A B C : (ι → ℝ) → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    (hC : BddSmooth 0 C) (hAn : ∀ y, 0 ≤ A y) (hBn : ∀ y, 0 ≤ B y)
    {c : ℝ} (hCB : ∀ y, (C y)^2 ≤ c^2*A y*B y)
    (pre : List (GaussianStep ι)) (hp : ∀ st ∈ pre, 0 < st.1) (x : ι → ℝ) :
    (prefixTest pre F C x)^2 ≤
      c^2*prefixTest pre F A x*prefixTest pre F B x := by
  have hGram (t : ℝ) (y : ι → ℝ) :
      0 ≤ t^2*A y - 2*t*C y + c^2*B y := by
    apply quadratic_nonneg_of_gram (hAn y) (mul_nonneg (sq_nonneg c) (hBn y))
    nlinarith [hCB y]
  have hQ (t : ℝ) : 0 ≤
      t^2*prefixTest pre F A x - 2*t*prefixTest pre F C x +
        c^2*prefixTest pre F B x := by
    have hh := prefixTest_nonneg hF (hGram t) pre hp x
    have he : (fun y => t^2*A y-2*t*C y+c^2*B y) =
        fun y => t^2*A y+(-2*t)*C y+c^2*B y := by funext y; ring
    have hscale : prefixTest pre F (fun y => t^2*A y) x =
        t^2*prefixTest pre F A x := by
      simpa only [zero_add] using prefixTest_affine hF hA pre hp 0 (t^2) x
    rw [he, prefixTest_add_const_mul hF
      ((hA.const_mul (t^2)).add (hC.const_mul (-2*t))) hB pre hp (c^2) x,
      prefixTest_add_const_mul hF (hA.const_mul (t^2)) hC pre hp (-2*t) x,
      hscale] at hh
    simpa only [zero_add, sub_eq_add_neg, neg_mul] using hh
  have hh := gram_of_quadratic_nonneg
    (prefixTest_nonneg hF hAn pre hp x)
    (mul_nonneg (sq_nonneg c) (prefixTest_nonneg hF hBn pre hp x)) hQ
  convert hh using 1
  ring

end OAI.SKFluctuations.Cavity
