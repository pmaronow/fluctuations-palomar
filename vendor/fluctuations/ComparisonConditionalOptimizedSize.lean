module

public import ComparisonConditionalErrorSize
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology BigOperators
set_option maxHeartbeats 7200000

theorem comparison_conditional_inner_optimized_cost {N delta E lam e v : ℝ}
    (hN : 0<N) (hE : 0<E) (hlam : 0<lam)
    (he : N^(-delta)*lam≤e) (hv : comparisonSmallMass N E≤v) :
    lam*v*(comparisonConditionalScale N delta E lam/(N*e*v^2))^((2:ℝ)/3)≤
      N^(4*delta/3)*E := by
  let A := comparisonConditionalScale N delta E lam
  have hA : 0<A := comparison_conditional_scale_pos hN hE hlam
  have hvp : 0<v := (comparisonSmallMass_pos hN hE).trans_le hv
  have hep : 0<e := (mul_pos (Real.rpow_pos_of_pos hN _) hlam).trans_le he
  have hp : N^delta*N^(-delta)=1 := by rw [←Real.rpow_add hN];simp
  have hs := mul_le_mul_of_nonneg_left he (Real.rpow_pos_of_pos hN delta).le
  have hs' : lam≤N^delta*e := by simpa only [←mul_assoc,hp,one_mul] using hs
  have hs2 := pow_le_pow_left₀ hlam.le hs' 2
  have hp2 : (N^delta)^2=N^(2*delta) := by
    rw [←Real.rpow_mul_natCast hN.le]
    congr 1
    norm_num
    ring
  rw [mul_pow,hp2] at hs2
  have hm := mul_le_mul_of_nonneg_left hv (mul_pos hN hE).le
  have hm' : 1≤N*E*v := by
    have heq : (N*E)*comparisonSmallMass N E=1 := by unfold comparisonSmallMass;field_simp
    rw [heq] at hm
    simpa only [mul_assoc] using hm
  have hscale : lam*A^2=N^(2*delta)*N*E^2 := comparison_conditional_scale_square hN hlam
  have hbase : lam^3*A^2≤N^(4*delta)*E^3*N^2*e^2*v := by
    have hh := mul_le_mul_of_nonneg_right hs2 (show 0≤lam*A^2 by positivity)
    have ht := mul_le_mul_of_nonneg_left hm' (show 0≤N^(4*delta)*N*E^2*e^2 by positivity)
    have hpow : N^(2*delta)*N^(2*delta)=N^(4*delta) := by rw [←Real.rpow_add hN];congr 1;ring
    have hh' : lam^3*A^2≤N^(4*delta)*N*E^2*e^2 := by
      calc
        _=lam^2*(lam*A^2) := by ring
        _≤(N^(2*delta)*e^2)*(lam*A^2) := hh
        _=N^(4*delta)*N*E^2*e^2 := by rw [hscale];calc
          _=(N^(2*delta)*N^(2*delta))*N*E^2*e^2 := by ring
          _=_ := by rw [hpow]
    nlinarith
  have hcube : (lam*v*(A/(N*e*v^2))^((2:ℝ)/3))^3=
      lam^3*A^2/(N^2*e^2*v) := by
    rw [mul_pow,←Real.rpow_mul_natCast (show 0≤A/(N*e*v^2) by positivity)]
    norm_num
    field_simp
    <;> ring
  have htarget : (N^(4*delta/3)*E)^3=N^(4*delta)*E^3 := by
    rw [mul_pow,←Real.rpow_mul_natCast hN.le]
    congr 2
    norm_num
  have hc : (lam*v*(A/(N*e*v^2))^((2:ℝ)/3))^3≤(N^(4*delta/3)*E)^3 := by
    rw [hcube,htarget]
    exact (div_le_iff₀ (by positivity : 0<N^2*e^2*v)).mpr (by nlinarith [hbase])
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3≠0)).mp hc

theorem comparison_conditional_inner_optimized_enlarged {N delta E lam e v y C : ℝ}
    (hN : 0<N) (hE : 0<E) (hlam : 0<lam)
    (he : N^(-delta)*lam≤e) (hv : comparisonSmallMass N E≤v)
    (hy : 0≤y) (hC : 0≤C) (hyA : y≤C*comparisonConditionalScale N delta E lam) :
    lam*v*(y/(N*e*v^2))^((2:ℝ)/3)≤C^((2:ℝ)/3)*N^(4*delta/3)*E := by
  have hA := comparison_conditional_scale_pos (delta:=delta) hN hE hlam
  have hvp : 0<v := (comparisonSmallMass_pos hN hE).trans_le hv
  have hep : 0<e := (mul_pos (Real.rpow_pos_of_pos hN _) hlam).trans_le he
  have hden : 0<N*e*v^2 := by positivity
  have hh := Real.rpow_le_rpow (div_nonneg hy hden.le) (div_le_div_of_nonneg_right hyA hden.le) (by norm_num : (0:ℝ)≤2/3)
  have heq : (C*comparisonConditionalScale N delta E lam/(N*e*v^2))^((2:ℝ)/3)=
      C^((2:ℝ)/3)*(comparisonConditionalScale N delta E lam/(N*e*v^2))^((2:ℝ)/3) := by
    rw [mul_div_assoc,Real.mul_rpow hC (by positivity)]
  rw [heq] at hh
  have hb := comparison_conditional_inner_optimized_cost hN hE hlam he hv
  have h1 := mul_le_mul_of_nonneg_left hh (mul_nonneg hlam.le hvp.le)
  have h2 := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hC ((2:ℝ)/3))
  nlinarith

theorem comparison_conditional_outer_optimized_cost {N m gamma d E t L : ℝ}
    (hN : 0<N) (hgamma : 0<gamma) (hd : 0<d) (hE : 0<E)
    (ht : 0≤t) (hL : 0≤L) (htd : t≤d^3*L)
    (hlower : gamma*N^(-(2:ℝ)/3+m)*d≤E) :
    N^(-(2:ℝ)/3)*t^((1:ℝ)/3)≤(1/gamma)*N^(-m)*L^((1:ℝ)/3)*E := by
  have hroot := Real.rpow_le_rpow ht htd (by norm_num : (0:ℝ)≤1/3)
  have hdroot : (d^3)^((1:ℝ)/3)=d := by
    rw [←Real.rpow_natCast d 3,←Real.rpow_mul hd.le]
    norm_num
  rw [Real.mul_rpow (by positivity) hL,hdroot] at hroot
  have hscale : N^(-(2:ℝ)/3)*d≤(1/gamma)*N^(-m)*E := by
    have hh := mul_le_mul_of_nonneg_left hlower (show 0≤(1/gamma)*N^(-m) by positivity)
    have heq : (1/gamma)*N^(-m)*(gamma*N^(-(2:ℝ)/3+m)*d)=N^(-(2:ℝ)/3)*d := by
      calc
        _=((1/gamma)*gamma)*(N^(-m)*N^(-(2:ℝ)/3+m))*d := by ring
        _=_ := by rw [one_div_mul_cancel hgamma.ne',one_mul,←Real.rpow_add hN];congr 2;ring
    rwa [heq] at hh
  have h1 := mul_le_mul_of_nonneg_left hroot (Real.rpow_pos_of_pos hN (-(2:ℝ)/3)).le
  have h2 := mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hL ((1:ℝ)/3))
  nlinarith

theorem comparison_log_loss_eventually {C p eps : ℝ} (hC : 0≤C) (heps : 0<eps) :
    ∀ᶠ N : ℝ in atTop, C*(Real.log N)^p≤N^eps := by
  have hsmall := isLittleO_log_rpow_rpow_atTop p heps
  have hh := hsmall.bound (show 0<1/(C+1) by positivity)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with N hbound hN
  have hlog : 0≤Real.log N := (Real.log_pos (lt_of_le_of_lt (by norm_num : (1:ℝ)≤1) hN)).le
  have hNp : 0<N := zero_lt_one.trans hN
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (Real.rpow_pos_of_pos hNp _).le] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound hC
  have hfrac : C*(1/(C+1))≤1 := by
    rw [←div_eq_mul_one_div]
    exact (div_le_iff₀ (by positivity : 0<C+1)).mpr (by linarith)
  have ht := mul_le_mul_of_nonneg_right hfrac (Real.rpow_pos_of_pos hNp eps).le
  nlinarith

theorem comparison_finite_group_sum_le {ι : Type*} (F : Finset ι)
    {N E exponent margin : ℝ} (hN : 0<N) (hE : 0≤E)
    (cost : ι→ℝ) (loss : ℝ) (hloss : 0≤loss)
    (hcost : ∀i∈F,cost i≤loss*N^exponent*E)
    (hcount : (F.card:ℝ)*loss≤N^margin) :
    ∑i∈F,cost i≤N^(exponent+margin)*E := by
  calc
    _≤∑i∈F,loss*N^exponent*E := Finset.sum_le_sum hcost
    _=(F.card:ℝ)*loss*N^exponent*E := by simp;ring
    _≤N^margin*N^exponent*E := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcount (Real.rpow_pos_of_pos hN exponent).le) hE
    _=N^(exponent+margin)*E := by rw [←Real.rpow_add hN];congr 2;ring

end OAI.SKFluctuations.LaplaceWindowFormalization
