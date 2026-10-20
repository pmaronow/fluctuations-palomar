module
public import SKConstants.ScalarProcessNestedIntegral

@[expose] public section
noncomputable section
open Filter
open scoped NNReal Topology
namespace SKConstants

def brownianDyadicGrid (T : ℝ≥0) : ScalarDyadicNestedGrid where
  time l i := T * (i : ℝ≥0) / (2 : ℝ≥0)^l
  monotone l := by
    intro i j hij
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hij)
      T.coe_nonneg) (by positivity)
  embed l d i := by
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add]
    field_simp
  zero l := by simp

@[simp] lemma brownianDyadicGrid_time_coe (T : ℝ≥0) (l i : ℕ) :
    ((brownianDyadicGrid T).time l i : ℝ) = (T : ℝ)*(i : ℝ)/(2 : ℝ)^l := by
  simp [brownianDyadicGrid]

@[simp] lemma brownianDyadicGrid_horizon (T : ℝ≥0) :
    (brownianDyadicGrid T).time 0 1 = T := by
  simp [brownianDyadicGrid]

def brownianDyadicWidth (T : ℝ≥0) (l : ℕ) : ℝ := (T : ℝ)/(2 : ℝ)^l

lemma brownianDyadicWidth_tendsto (T : ℝ≥0) :
    Tendsto (brownianDyadicWidth T) atTop (𝓝 0) := by
  change Tendsto (fun l => (T : ℝ)/(2 : ℝ)^l) atTop (𝓝 0)
  have h := (tendsto_const_nhds (x := (T : ℝ))).mul
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num))
  simpa [brownianDyadicWidth,div_eq_mul_inv,inv_pow,one_div] using h

lemma brownianDyadicGrid_width_le (T : ℝ≥0) (l i : ℕ) :
    ((brownianDyadicGrid T).time l (i+1) : ℝ)-(brownianDyadicGrid T).time l i ≤
      brownianDyadicWidth T l := by
  simp only [brownianDyadicGrid_time_coe,brownianDyadicWidth,Nat.cast_add,Nat.cast_one]
  exact le_of_eq (by ring)

lemma brownianDyadicGrid_left_le (T : ℝ≥0) (l d i : ℕ) :
    |((brownianDyadicGrid T).time (l+d) i : ℝ)-(brownianDyadicGrid T).time l (i/2^d)| ≤
      brownianDyadicWidth T l := by
  have hlow := (brownianDyadicGrid T).left_le l d i
  rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlow))]
  have hu : (i : ℝ) ≤ (i/2^d : ℕ)*(2 : ℝ)^d+(2 : ℝ)^d := by
    exact_mod_cast (Nat.lt_div_mul_add (a := i) (pow_pos (by decide : 0 < 2) d)).le
  simp only [brownianDyadicGrid_time_coe,brownianDyadicWidth,pow_add]
  have hp : 0 < (2 : ℝ)^l*(2 : ℝ)^d := by positivity
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ)^l)).mpr
  have huT := mul_le_mul_of_nonneg_left hu T.coe_nonneg
  field_simp at *
  nlinarith

end SKConstants
