module

public import ComparisonActualGeneralLocalThermalFactorIntegralBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory
open scoped Topology
set_option autoImplicit false

theorem power_factor_le_epsilon_add_linear
    (k : ℕ) {eta x epsilon : ℝ} (heta : 0 ≤ eta) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hpow : eta^(k+1) ≤ x) :
    eta ≤ epsilon+x/epsilon^k := by
  by_cases hsmall : eta ≤ epsilon
  · have hquot : 0 ≤ x/epsilon^k := div_nonneg hx (pow_pos hepsilon _).le
    linarith
  · have hlarge : epsilon ≤ eta := le_of_lt (lt_of_not_ge hsmall)
    have hk : epsilon^k ≤ eta^k := pow_le_pow_left₀ hepsilon.le hlarge _
    have hmain : eta*epsilon^k ≤ x := by
      calc
        eta*epsilon^k ≤ eta*eta^k := mul_le_mul_of_nonneg_left hk heta
        _ = eta^(k+1) := by rw [pow_succ]; ring
        _ ≤ x := hpow
    have hquot : eta ≤ x/epsilon^k :=
      (le_div_iff₀ (pow_pos hepsilon _)).mpr (by nlinarith only [hmain])
    linarith

theorem power_factor_integral_epsilon_bound
    (k : ℕ) {d Ccut K site epsilon : ℝ}
    (hd : 0 < d) (hCcut : 0 ≤ Ccut) (hK : 0 ≤ K)
    (hsite : 0 ≤ site) (hepsilon : 0 < epsilon)
    (D Eta : ℝ → ℝ)
    (hD : IntervalIntegrable D volume 0 (Ccut*d))
    (hEta : IntervalIntegrable Eta volume 0 (Ccut*d))
    (hDpos : ∀u∈Icc (0:ℝ) (Ccut*d),0≤D u)
    (hEtapos : ∀u∈Icc (0:ℝ) (Ccut*d),0≤Eta u)
    (hpow : ∀u∈Icc (0:ℝ) (Ccut*d),
      (Eta u)^(k+1) ≤ K*(D u+site)/d) :
    (∫u in 0..Ccut*d,Eta u)/d ≤
      Ccut*epsilon+K/epsilon^k*
        ((∫u in 0..Ccut*d,D u)/d^2+Ccut*site/d) := by
  have hbound : ∀u∈Icc (0:ℝ) (Ccut*d),
      Eta u ≤ epsilon+(K/(d*epsilon^k))*(D u+site) := by
    intro u hu
    have hx : 0 ≤ K*(D u+site)/d :=
      div_nonneg (mul_nonneg hK (add_nonneg (hDpos u hu) hsite)) hd.le
    have H:=power_factor_le_epsilon_add_linear k (hEtapos u hu) hx hepsilon (hpow u hu)
    convert H using 1; field_simp
  have hint : IntervalIntegrable (fun u=>epsilon+(K/(d*epsilon^k))*(D u+site))
      volume 0 (Ccut*d) := intervalIntegrable_const.add
        ((hD.add intervalIntegrable_const).const_mul _)
  have H:=intervalIntegral.integral_mono_on (mul_nonneg hCcut hd.le) hEta hint hbound
  have HI : ∫u in 0..Ccut*d,D u+site =
      (∫u in 0..Ccut*d,D u)+site*(Ccut*d) := by
    rw [intervalIntegral.integral_add hD intervalIntegrable_const]
    simp only [intervalIntegral.integral_const,smul_eq_mul,sub_zero]
    ring
  simp only [intervalIntegral.integral_add intervalIntegrable_const
    ((hD.add intervalIntegrable_const).const_mul _),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const,smul_eq_mul,sub_zero] at H
  rw [HI] at H
  have hdiv := div_le_div_of_nonneg_right H hd.le
  convert hdiv using 1; field_simp

theorem power_factor_normalized_integral_tendsto_zero
    (k : ℕ) {Ccut K : ℝ} (hCcut : 0 ≤ Ccut) (hK : 0 ≤ K)
    (d site : ℕ → ℝ) (D Eta : ℕ → ℝ → ℝ)
    (hd : ∀n, 0 < d n) (hsite : ∀n, 0 ≤ site n)
    (hIlim : Tendsto
      (fun n => (∫u in 0..Ccut*d n,D n u)/(d n)^2) atTop (𝓝 0))
    (hsitelim : Tendsto (fun n => site n/d n) atTop (𝓝 0))
    (hD : ∀n, IntervalIntegrable (D n) volume 0 (Ccut*d n))
    (hEta : ∀n, IntervalIntegrable (Eta n) volume 0 (Ccut*d n))
    (hDpos : ∀n,∀u∈Icc (0:ℝ) (Ccut*d n),0≤D n u)
    (hEtapos : ∀n,∀u∈Icc (0:ℝ) (Ccut*d n),0≤Eta n u)
    (hpow : ∀n,∀u∈Icc (0:ℝ) (Ccut*d n),
      (Eta n u)^(k+1) ≤ K*(D n u+site n)/d n) :
    Tendsto (fun n => (∫u in 0..Ccut*d n,Eta n u)/d n) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le
      (div_nonneg (intervalIntegral.integral_nonneg
        (mul_nonneg hCcut (hd n).le) (hEtapos n)) (hd n).le))
  · intro y hy
    let eps := y/(Ccut+1)
    have hden : 0 < Ccut+1 := by linarith
    have heps : 0 < eps := div_pos hy hden
    have hsmall : Ccut*eps < y := by
      have heq : eps*(Ccut+1)=y := by
        dsimp [eps]
        exact div_mul_cancel₀ y hden.ne'
      nlinarith
    have hlim : Tendsto
        (fun n => Ccut*eps+K/eps^k*
          ((∫u in 0..Ccut*d n,D n u)/(d n)^2+Ccut*site n/d n))
        atTop (𝓝 (Ccut*eps)) := by
      have H := (hIlim.add (hsitelim.const_mul Ccut)).const_mul (K/eps^k)
      have H' : Tendsto
          (fun n => Ccut*eps+K/eps^k*
            ((∫u in 0..Ccut*d n,D n u)/(d n)^2+Ccut*(site n/d n)))
          atTop (𝓝 (Ccut*eps+K/eps^k*(0+Ccut*0))) :=
        tendsto_const_nhds.add H
      simpa only [mul_zero, add_zero, div_eq_mul_inv, mul_assoc] using H'
    filter_upwards [(tendsto_order.mp hlim).2 y hsmall] with n hn
    have HB := power_factor_integral_epsilon_bound k
      (hd n) hCcut hK (hsite n) heps (D n) (Eta n)
      (hD n) (hEta n) (hDpos n) (hEtapos n) (hpow n)
    exact HB.trans_lt hn

end OAI.SKFluctuations.Cavity
