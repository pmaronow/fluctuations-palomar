module

public import SKConstants.ParisiCDFPotentialExpectation

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat

lemma BoundedSmoothFamily.static {g : ℝ → ℝ} (hg : BoundedSmooth g) :
    BoundedSmoothFamily (fun (_t : ℝ) => g) := by
  refine ⟨hg.smooth.continuous.measurable.comp measurable_snd,fun _ => hg,?_⟩
  intro n
  obtain ⟨C,hC⟩ := hg.bounds n
  exact ⟨C,fun _ x => hC x⟩

def staticTimeField (T : ℝ) (g : ℝ → ℝ) (hg : BoundedSmooth g) : TimeField T where
  f := fun _ => g
  d := fun _ _ => 0
  smooth := BoundedSmoothFamily.static hg
  rate_smooth := BoundedSmoothFamily.timeConst measurable_const (C:=0) (by simp)
  continuous := hg.smooth.continuous.comp continuous_snd
  rate_right := fun _ _ => continuousWithinAt_const
  time_deriv := fun _ _ _ _ => hasDerivWithinAt_const _ _ _

def scalarSmoothCutoff (n : ℕ) (x : ℝ) : ℝ :=
  ((n+1:ℕ):ℝ)*Real.tanh ((parisiGridMesh n:ℝ)*x)

lemma scalarSmoothCutoff_boundedSmooth (n : ℕ) : BoundedSmooth (scalarSmoothCutoff n) :=
  (boundedSmooth_tanh_mul (parisiGridMesh n:ℝ)).const_mul ((n+1:ℕ):ℝ)

lemma scalarSmoothCutoff_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (scalarSmoothCutoff n) (1-(Real.tanh ((parisiGridMesh n:ℝ)*x))^2) x := by
  have HE : ((n+1:ℕ):ℝ)*(parisiGridMesh n:ℝ)=1 := by exact_mod_cast parisiGridMesh_horizon n
  have H := ((hasDerivAt_tanh ((parisiGridMesh n:ℝ)*x)).comp x
    ((hasDerivAt_id x).const_mul (parisiGridMesh n:ℝ))).const_mul ((n+1:ℕ):ℝ)
  convert H using 1
  · rfl
  · symm
    calc
      ((n+1:ℕ):ℝ)*((1-(Real.tanh ((parisiGridMesh n:ℝ)*x))^2)*((parisiGridMesh n:ℝ)*1)) =
        (((n+1:ℕ):ℝ)*(parisiGridMesh n:ℝ))*(1-(Real.tanh ((parisiGridMesh n:ℝ)*x))^2) := by ring
      _ = _ := by rw [HE]; ring

lemma scalarSmoothCutoff_deriv (n : ℕ) (x : ℝ) :
    deriv (scalarSmoothCutoff n) x=1-(Real.tanh ((parisiGridMesh n:ℝ)*x))^2 :=
  (scalarSmoothCutoff_hasDerivAt n x).deriv

lemma scalarSmoothCutoff_second_deriv (n : ℕ) (x : ℝ) :
    deriv (deriv (scalarSmoothCutoff n)) x=
      -2*(parisiGridMesh n:ℝ)*Real.tanh ((parisiGridMesh n:ℝ)*x)*
        (1-(Real.tanh ((parisiGridMesh n:ℝ)*x))^2) := by
  have HE : deriv (scalarSmoothCutoff n)=fun y => 1-(Real.tanh ((parisiGridMesh n:ℝ)*y))^2 :=
    funext (scalarSmoothCutoff_deriv n)
  rw [HE]
  have H := (hasDerivAt_const x (1:ℝ)).sub
    (((hasDerivAt_tanh ((parisiGridMesh n:ℝ)*x)).comp x
      ((hasDerivAt_id x).const_mul (parisiGridMesh n:ℝ))).pow 2)
  have HD : HasDerivAt (fun y => 1-(Real.tanh ((parisiGridMesh n:ℝ)*y))^2)
      (-2*(parisiGridMesh n:ℝ)*Real.tanh ((parisiGridMesh n:ℝ)*x)*
        (1-(Real.tanh ((parisiGridMesh n:ℝ)*x))^2)) x := by
    convert H using 1 <;> simp only [Function.comp_def,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] <;> first | rfl | ring
  exact HD.deriv

lemma scalarSmoothCutoff_deriv_bounds (n : ℕ) (x : ℝ) :
    0≤deriv (scalarSmoothCutoff n) x ∧ deriv (scalarSmoothCutoff n) x≤1 := by
  rw [scalarSmoothCutoff_deriv]
  have HT := Real.abs_tanh_lt_one ((parisiGridMesh n:ℝ)*x)
  have HS : (Real.tanh ((parisiGridMesh n:ℝ)*x))^2≤1 := by
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) HT.le 2
  constructor <;> nlinarith [sq_nonneg (Real.tanh ((parisiGridMesh n:ℝ)*x))]

lemma scalarSmoothCutoff_lipschitz (n : ℕ) : LipschitzWith 1 (scalarSmoothCutoff n) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((scalarSmoothCutoff_boundedSmooth n).smooth.differentiable (by simp))
  intro x
  have H := scalarSmoothCutoff_deriv_bounds n x
  exact_mod_cast (by simpa only [Real.norm_eq_abs,abs_of_nonneg H.1] using H.2 : ‖deriv (scalarSmoothCutoff n) x‖≤(1:ℝ))

lemma scalarSmoothCutoff_abs_le (n : ℕ) (x : ℝ) : |scalarSmoothCutoff n x|≤|x| := by
  have H := (scalarSmoothCutoff_lipschitz n).norm_sub_le x 0
  simpa only [scalarSmoothCutoff,mul_zero,Real.tanh_zero,sub_zero,Real.norm_eq_abs,
    NNReal.coe_one,one_mul] using H

lemma scalarSmoothCutoff_second_deriv_bound (n : ℕ) (x : ℝ) :
    |deriv (deriv (scalarSmoothCutoff n)) x|≤2*(parisiGridMesh n:ℝ) := by
  rw [scalarSmoothCutoff_second_deriv,abs_mul,abs_mul,abs_mul]
  have HT := (Real.abs_tanh_lt_one ((parisiGridMesh n:ℝ)*x)).le
  have HD := scalarSmoothCutoff_deriv_bounds n x
  rw [scalarSmoothCutoff_deriv] at HD
  simp only [abs_of_nonneg (parisiGridMesh n).coe_nonneg,abs_of_nonneg HD.1]
  norm_num
  nlinarith [mul_le_mul HT HD.2 HD.1 (by norm_num : (0:ℝ)≤1)]

lemma scalarSmoothCutoff_tendsto (x : ℝ) :
    Tendsto (fun n => scalarSmoothCutoff n x) atTop (𝓝 x) := by
  by_cases hx : x=0
  · subst x
    simp only [scalarSmoothCutoff,mul_zero,Real.tanh_zero]
    exact tendsto_const_nhds
  have HT : HasDerivAt Real.tanh 1 0 := by simpa only [Real.tanh_zero,zero_pow (by decide : (2:ℕ)≠0),sub_zero] using hasDerivAt_tanh 0
  have HC := HT.continuousAt_div
  have HH := (parisiGridMesh_coe_tendsto.mul_const x)
  simp only [zero_mul] at HH
  have HF := HC.tendsto.comp HH
  have HE (n : ℕ) : ((parisiGridMesh n:ℝ)*x)≠0 := mul_ne_zero (ne_of_gt (parisiGridMesh_pos n)) hx
  simp only [Function.comp_def,Function.update_of_ne (HE _),Function.update_self,Real.tanh_zero,sub_zero] at HF
  have HR := HF.const_mul x
  simp only [mul_one] at HR
  convert HR using 1
  funext n
  unfold scalarSmoothCutoff
  simp only [parisiGridMesh,NNReal.coe_div,NNReal.coe_one,NNReal.coe_add,NNReal.coe_natCast,
    Nat.cast_add,Nat.cast_one]
  field_simp

lemma scalarSmoothCutoff_deriv_tendsto (x : ℝ) :
    Tendsto (fun n => deriv (scalarSmoothCutoff n) x) atTop (𝓝 1) := by
  have H := contDiff_tanh.continuous.continuousAt.tendsto.comp (parisiGridMesh_coe_tendsto.mul_const x)
  simp only [zero_mul,Real.tanh_zero] at H
  simpa only [Function.comp_def,scalarSmoothCutoff_deriv,zero_pow (by decide : (2:ℕ)≠0),sub_zero] using (tendsto_const_nhds (x:=(1:ℝ))).sub (H.pow 2)

lemma scalarSmoothCutoff_second_deriv_tendsto (x : ℝ) :
    Tendsto (fun n => deriv (deriv (scalarSmoothCutoff n)) x) atTop (𝓝 0) := by
  have H := contDiff_tanh.continuous.continuousAt.tendsto.comp (parisiGridMesh_coe_tendsto.mul_const x)
  simp only [zero_mul,Real.tanh_zero] at H
  simpa only [Function.comp_def,scalarSmoothCutoff_second_deriv,scalarSmoothCutoff_deriv,zero_mul,mul_zero] using
    (((parisiGridMesh_coe_tendsto.const_mul (-2:ℝ)).mul H).mul
      (scalarSmoothCutoff_deriv_tendsto x))

end SKConstants.ParisiFullSupport
