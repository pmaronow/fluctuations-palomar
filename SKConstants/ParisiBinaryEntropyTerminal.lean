module

public import SKConstants.ParisiBinaryEntropyBounds

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.ParisiFullSupport

theorem binarySpinEntropy_tanh (y : ℝ) :
    binarySpinEntropy (Real.tanh y)=Real.log (2*Real.cosh y)-y*Real.tanh y := by
  have hC : Real.cosh y≠0 := (Real.cosh_pos y).ne'
  have hE : Real.exp y+Real.exp (-y)≠0 := by positivity
  have hP : 1+Real.tanh y=Real.exp y/Real.cosh y := by
    rw [Real.tanh_eq,Real.cosh_eq]
    field_simp
    ring
  have hM : 1-Real.tanh y=Real.exp (-y)/Real.cosh y := by
    rw [Real.tanh_eq,Real.cosh_eq]
    field_simp
    ring
  rw [binarySpinEntropy_log_formula _ (Real.abs_tanh_lt_one y)]
  rw [hP,hM,Real.log_div (Real.exp_pos y).ne' hC,
    Real.log_div (Real.exp_pos (-y)).ne' hC,Real.log_exp,Real.log_exp,
    Real.log_mul (by norm_num) hC]
  rw [←hP,←hM]
  ring

end SKConstants.ParisiFullSupport
