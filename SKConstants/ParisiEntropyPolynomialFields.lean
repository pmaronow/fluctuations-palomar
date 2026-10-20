module

public import SKConstants.ParisiSmoothCutoffs
public import SKConstants.ParisiBinaryEntropyBounds

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat
variable {T : ℝ}

def powerTimeField (F : TimeField T) : ℕ → TimeField T
  | 0 => staticTimeField T (fun _ => 1) (BoundedSmooth.const 1)
  | n+1 => (powerTimeField F n).mul F

lemma powerTimeField_f (F : TimeField T) (n : ℕ) (t x : ℝ) :
    (powerTimeField F n).f t x=(F.f t x)^n := by
  induction n with
  | zero => simp only [powerTimeField,staticTimeField,pow_zero]
  | succ n ih => simp only [powerTimeField,TimeField.mul,ih,pow_succ]

lemma powerTimeField_deriv (F : TimeField T) (n : ℕ) (t x : ℝ) :
    deriv ((powerTimeField F n).f t) x=(n:ℝ)*(F.f t x)^(n-1)*deriv (F.f t) x := by
  have HE : (powerTimeField F n).f t=fun y => (F.f t y)^n := funext (powerTimeField_f F n t)
  rw [HE]
  exact ((((F.smooth.regular t).smooth.differentiable (by simp) x).hasDerivAt).pow n).deriv

lemma powerTimeField_generator_zero (F : TimeField T) (b : ℝ → ℝ → ℝ) (t x : ℝ)
    (hF : F.generator b t x=0) (n : ℕ) :
    (powerTimeField F n).generator b t x=
      ((n:ℝ)*((n-1:ℕ):ℝ)/2)*(F.f t x)^(n-2)*(deriv (F.f t) x)^2 := by
  induction n with
  | zero => simp only [powerTimeField,TimeField.generator,staticTimeField,deriv_const',deriv_const,Nat.cast_zero,
      zero_mul,mul_zero,zero_add,zero_div,add_zero]
  | succ n ih =>
    rw [powerTimeField,TimeField.generator_mul,hF,ih,powerTimeField_f,powerTimeField_deriv]
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => norm_num;ring
      | succ n =>
        simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.add_sub_cancel,
          Nat.add_sub_cancel_right,Nat.succ_eq_add_one,mul_zero,zero_add]
        rw [show n+1+1-2=n by omega,show n+1+1+1-2=n+1 by omega]
        rw [pow_succ]
        ring

def entropyPolynomialTimeField (F : TimeField T) : ℕ → TimeField T
  | 0 => staticTimeField T (fun _ => Real.log 2) (BoundedSmooth.const _)
  | N+1 => (entropyPolynomialTimeField F N).add
      ((powerTimeField F (2*N+2)).const_mul (-1/(((2*N+1:ℕ):ℝ)*((2*N+2:ℕ):ℝ))))

lemma entropyPolynomialTimeField_f (F : TimeField T) (N : ℕ) (t x : ℝ) :
    (entropyPolynomialTimeField F N).f t x=binaryEntropyPolynomial N (F.f t x) := by
  induction N with
  | zero => simp only [entropyPolynomialTimeField,staticTimeField,binaryEntropyPolynomial,sum_range_zero,sub_zero]
  | succ N ih =>
    simp only [entropyPolynomialTimeField,TimeField.add,TimeField.const_mul,ih,powerTimeField_f,
      binaryEntropyPolynomial,sum_range_succ]
    ring

lemma entropyPolynomialTimeField_generator (F : TimeField T) (b : ℝ → ℝ → ℝ)
    (t x : ℝ) (hF : F.generator b t x=0) (N : ℕ) :
    (entropyPolynomialTimeField F N).generator b t x=
      -(1/2:ℝ)*(deriv (F.f t) x)^2*(∑ k∈range N, (F.f t x)^(2*k)) := by
  induction N with
  | zero => simp only [entropyPolynomialTimeField,TimeField.generator,staticTimeField,deriv_const',deriv_const,
      zero_mul,mul_zero,zero_add,add_zero,sum_range_zero]
  | succ N ih =>
    rw [entropyPolynomialTimeField,TimeField.generator_add,TimeField.generator_const_mul,
      ih,powerTimeField_generator_zero F b t x hF]
    rw [sum_range_succ]
    have HE1 : 2*N+2-1=2*N+1 := by omega
    have HE2 : 2*N+2-2=2*N := by omega
    rw [HE1,HE2]
    have H1 : ((2*N+1:ℕ):ℝ)≠0 := by positivity
    have H2 : ((2*N+2:ℕ):ℝ)≠0 := by positivity
    field_simp
    ring

end SKConstants.ParisiFullSupport
