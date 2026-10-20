module

public import Mathlib

@[expose] public section

open Set Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SKConstants.ParisiFullSupport

def binarySpinEntropy (m : ℝ) : ℝ := Real.binEntropy ((1+m)/2)

def binaryEntropyPolynomial (N : ℕ) (m : ℝ) : ℝ :=
  Real.log 2-∑ k∈range N, m^(2*k+2)/(((2*k+1:ℕ):ℝ)*((2*k+2:ℕ):ℝ))

lemma hasSum_log_second_primitive {x : ℝ} (hx : |x|<1) :
    HasSum (fun n : ℕ => x^(n+2)/(((n+1:ℕ):ℝ)*((n+2:ℕ):ℝ)))
      ((1-x)*Real.log (1-x)+x) := by
  have H : HasSum (fun n : ℕ => x^(n+1)/((n+1:ℕ):ℝ)) (-Real.log (1-x)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using Real.hasSum_pow_div_log_of_abs_lt_one hx
  have Hs := (hasSum_nat_add_iff' (f:=fun n : ℕ => x^(n+1)/((n+1:ℕ):ℝ)) 1).mpr H
  simp only [sum_range_one,Nat.zero_add,pow_one,Nat.cast_one,div_one,Nat.add_assoc] at Hs
  have HR := (H.mul_left x).sub Hs
  convert HR using 1
  · funext n
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    rw [show n+2=(n+1)+1 by omega,pow_succ]
    have hn1 : (n:ℝ)+1≠0 := by positivity
    have hn2 : (n:ℝ)+2≠0 := by positivity
    field_simp
    ring
  · ring

lemma binarySpinEntropy_log_formula (x : ℝ) (hx : |x|<1) :
    binarySpinEntropy x=Real.log 2-
      (1/2:ℝ)*((1-x)*Real.log (1-x)+(1+x)*Real.log (1+x)) := by
  have hm : 0<1-x := by linarith [(abs_lt.mp hx).2]
  have hp : 0<1+x := by linarith [(abs_lt.mp hx).1]
  unfold binarySpinEntropy
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,Real.negMulLog_def]
  dsimp only
  rw [show 1-(1+x)/2=(1-x)/2 by ring]
  rw [Real.log_div hp.ne' (by norm_num),Real.log_div hm.ne' (by norm_num)]
  ring

theorem binarySpinEntropy_hasSum {x : ℝ} (hx : |x|<1) :
    HasSum (fun k : ℕ => x^(2*k+2)/(((2*k+1:ℕ):ℝ)*((2*k+2:ℕ):ℝ)))
      (Real.log 2-binarySpinEntropy x) := by
  let term := fun n : ℕ => (1/2:ℝ)*
    (x^(n+2)/(((n+1:ℕ):ℝ)*((n+2:ℕ):ℝ))+
      (-x)^(n+2)/(((n+1:ℕ):ℝ)*((n+2:ℕ):ℝ)))
  have H := ((hasSum_log_second_primitive hx).add
    (hasSum_log_second_primitive (x:=-x) (by simpa only [abs_neg] using hx))).mul_left (1/2:ℝ)
  have HE : term ∘ (2*·)=fun k : ℕ => x^(2*k+2)/(((2*k+1:ℕ):ℝ)*((2*k+2:ℕ):ℝ)) := by
    funext k
    dsimp only [term,Function.comp_def]
    rw [(show Even (2*k+2) from ⟨k+1,by omega⟩).neg_pow]
    ring
  rw [←HE,(mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff]
  · have HT : Real.log 2-binarySpinEntropy x=
        (1/2:ℝ)*((1-x)*Real.log (1-x)+x+((1- -x)*Real.log (1- -x)+ -x)) := by
      rw [binarySpinEntropy_log_formula x hx]
      simp only [sub_neg_eq_add]
      ring
    rw [HT]
    exact H
  · intro m hm
    rw [range_two_mul,Set.mem_ofPred_eq] at hm
    have hodd : Odd (m+2) := (Nat.not_even_iff_odd.mp hm).add_even (by decide : Even 2)
    dsimp only [term]
    rw [hodd.neg_pow]
    ring

theorem binaryEntropyPolynomial_tendsto {x : ℝ} (hx : |x|<1) :
    Tendsto (fun N => binaryEntropyPolynomial N x) atTop (𝓝 (binarySpinEntropy x)) := by
  have H := (binarySpinEntropy_hasSum hx).tendsto_sum_nat
  have HR := (tendsto_const_nhds (x:=Real.log 2)).sub H
  simpa only [binaryEntropyPolynomial,sub_sub_cancel] using HR

end SKConstants.ParisiFullSupport
