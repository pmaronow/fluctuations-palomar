module

public import ComparisonNativeBroadTraceRates
public import ComparisonNativeOrdinaryPhysicalRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000

theorem native_inner_broad_remainder_le_core
    (m : NativeBandModel) {width C K eps : ℝ}
    (hw : 0 ≤ width) (hwb : width ≤ m.bandMass)
    (hUeq : m.U=comparisonSmallMass m.N m.E) (hU1 : m.U ≤ 1)
    (hLU : m.Lcap ≤ m.U) (hLlower : m.N^(-(1:ℝ)) ≤ m.Lcap)
    (hUA : m.U ≤ comparisonConditionalScale m.N m.delta m.E m.lam)
    (hvU : m.U ≤ m.bandMass) (hC : 0 ≤ C)
    (hvA : m.bandMass ≤ C*comparisonConditionalScale m.N m.delta m.E m.lam)
    (hyA : m.y ≤ C*comparisonConditionalScale m.N m.delta m.E m.lam)
    (hyN : m.y ≤ m.N) (hK : 1 ≤ K)
    (hstrength : m.N*(m.N^(-m.delta)*m.lam) ≤ K*m.P)
    (horder : (m.delta+2)/((m.l:ℝ)-1) ≤ eps) :
    m.groupStrength*width*(m.D0^2+m.reverse m.D0) ≤
      K*comparisonInnerPhysicalCore m.N m.delta m.E m.Q C m.capLogFactor eps := by
  have hratio := comparison_physical_reverse_ratio (delta:=m.delta) m.hN m.hlog m.hU
    hU1 hLlower m.hy.le hyN
  have hc := comparison_inner_ledger_with_strength_distortion m.hl m.hN m.hE m.hlam
    m.P_pos hK hstrength (hUeq ▸ hvU) hvA m.hy hyA m.D0_pos m.hQ hC
    m.capLogFactor_nonneg m.hLcap.le (hUeq ▸ hLU) (hUeq ▸ hUA)
    m.D0_eq_capLogFactor.le hratio horder
  change m.lam*m.bandMass*(2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
    3/(m.P*m.bandMass^2)+m.D0^2+m.reverse m.D0) ≤ _ at hc
  have hrest := m.reverse_nonneg m.D0_pos.le
  have hpositive : 0 ≤ 2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
      3/(m.P*m.bandMass^2) := by
    have := m.P_pos
    have := m.hy
    positivity
  have hstrengthL : m.groupStrength ≤ m.lam := laplaceComparisonStrength_le m.d m.hlam.le m.ag
  have hs := mul_le_mul hstrengthL hwb hw m.hlam.le
  have hmul := mul_le_mul_of_nonneg_right hs (add_nonneg (sq_nonneg m.D0) hrest)
  have hdrop := mul_nonneg (mul_pos m.hlam m.hbandMass).le hpositive
  nlinarith

theorem actual_native_inner_broad_error_eventually
    {delta Q C K Ccut Ko R V0 : ℝ}
    (hdelta : 0 < delta) (hC : 0 ≤ C) (hK : 1 ≤ K)
    (hcut : 3 ≤ Ccut) (hKo : 0 ≤ Ko) (hR : 0 ≤ R) (hV0 : 0 ≤ V0) :
    ∀ᶠ N : ℝ in atTop, ∀ (m : NativeBandModel) (g : NativeBroadSliceGeometry m),
      m.N=N → m.delta=delta → m.Q=Q →
      NativeOrdinaryPhysicalData m Ccut Ko 64 V0 → NativeBandRawMaster m →
      g.scale ≤ R*m.rho →
      (∫r in Ioo g.a g.b,deriv m.alpha.val.val r) ≤ m.bandMass →
      m.Lcap ≤ m.U → m.N^(-(1:ℝ)) ≤ m.Lcap →
      m.U ≤ comparisonConditionalScale m.N m.delta m.E m.lam →
      m.U ≤ m.bandMass →
      m.bandMass ≤ C*comparisonConditionalScale m.N m.delta m.E m.lam →
      m.y ≤ C*comparisonConditionalScale m.N m.delta m.E m.lam →
      m.N*(m.N^(-m.delta)*m.lam) ≤ K*m.P →
      (m.delta+2)/((m.l:ℝ)-1) ≤ delta →
      (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
        N^(6*delta)*m.E := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hCcut : 0 ≤ Ccut := by linarith
  have hF := comparison_log_loss_eventually (C:=(340+192*Ccut)*K) (p:=1) (by positivity) hdelta
  have hthree := comparison_log_loss_eventually (C:=3) (p:=0) (by norm_num) hdelta
  filter_upwards [native_broad_trace_coefficient_eventually (S:=Ccut) hdelta hKo hK0 hR hCcut,
    comparison_capLogFactor_eventually hdelta,
    comparison_inner_error_core_eventually (Q:=Q) hdelta hC,
    comparison_ordinary_cutoff_eventually (Q:=Q) (P0:=1) (V0:=V0) (by norm_num) hV0 hcut,
    hF,hthree,eventually_ge_atTop (4:ℝ)] with N htrace hJ hcore hrestore hFpow h3pow hN4
  intro m g hNeq hdeq hQeq data hraw hratio hwb hLU hLlower hUA hvU hvA hyA hstrength horder
  have hN : 1 ≤ N := by linarith
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hcutoff := comparison_physical_cutoff_log (C:=Ccut) hNp
  have hlogcut : Real.log (1/N^(-Ccut)) ≤ m.Lside := by rw [hcutoff.2,data.side,hNeq]
  have hsmall : 2*N^(-Ccut) < m.U := by
    have hp := Real.rpow_le_rpow_of_exponent_le hN (show -Ccut ≤ -(2:ℝ) by linarith)
    have he : N^(-(2:ℝ))=1/N^2 := by rw [Real.rpow_neg hNp.le,Real.rpow_two,one_div]
    rw [he] at hp
    have hl : 2/N^2 < 1/N := by field_simp; nlinarith
    have hUlo := data.U_lower
    rw [hNeq] at hUlo
    have hp' : 2*N^(-Ccut) ≤ 2/N^2 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ 2 by norm_num)
    exact hp'.trans_lt (hl.trans_le hUlo)
  have hstrengthL : m.groupStrength ≤ m.lam := laplaceComparisonStrength_le m.d m.hlam.le m.ag
  have hstrength' : m.N*m.groupStrength ≤ (K*N^delta)*m.P := by
    have hh := mul_le_mul_of_nonneg_left hstrength (Real.rpow_pos_of_pos hNp delta).le
    simp only [hNeq,hdeq] at hh ⊢
    have he : N^delta*(N*(N^(-delta)*m.lam))=N*m.lam := by
      rw [Real.rpow_neg hNp.le]
      field_simp
    rw [he] at hh
    have hs := mul_le_mul_of_nonneg_left hstrengthL hNp.le
    nlinarith
  have hb := actual_native_broad_physical_trace_error m g hraw hcutoff.1 hsmall
    data.left data.upper hlogcut data.U_eq (mul_nonneg hK0 (Real.rpow_pos_of_pos hNp _).le) hR
    hstrength' hratio
  dsimp only at hb
  have ht := htrace m.U m.Ko m.Lside (K*N^delta) m.hU data.U_le_one
    (hNeq ▸ data.U_lower) (zero_le_one.trans m.hKo) data.Ko_le m.hLside
    (by rw [data.side,hNeq]) (by positivity) le_rfl
  have hw := native_broad_slice_mass_bounds m g
  have hw0 := hw.1.le
  have hr := native_inner_broad_remainder_le_core m hw.1.le hwb data.U_eq data.U_le_one
    hLU hLlower hUA hvU hC hvA hyA data.y_upper hK hstrength horder
  let F := (340+192*m.Lside)*K/3
  have hF0 : 0 ≤ F := by dsimp [F]; have := m.hLside; positivity
  have hFN : F ≤ N^delta := by
    have hlg := hNeq ▸ m.hlog
    have hh : (340+192*m.Lside)*K ≤ ((340+192*Ccut)*K)*Real.log N := by
      rw [data.side,hNeq]
      have hp := mul_le_mul_of_nonneg_right hlg (show 0 ≤ 340*K by positivity)
      nlinarith
    dsimp [F]
    simp only [Real.rpow_one] at hFpow
    have hp : 0 ≤ N^delta := (Real.rpow_pos_of_pos hNp _).le
    apply (div_le_iff₀ (show (0:ℝ) < 3 by norm_num)).mpr
    exact (hh.trans hFpow).trans (by nlinarith only [hp])
  have hJ1 : m.capLogFactor ≤ 1 := by
    unfold NativeBandModel.capLogFactor
    rw [hNeq,hdeq]
    exact hJ m.U m.hU data.U_le_one (hNeq ▸ data.U_lower)
  have hmain := hcore m.E F m.capLogFactor delta m.hE.le hF0 hFN
    m.capLogFactor_nonneg hJ1 le_rfl
  have hDterm : 0 ≤ 16*m.capLogFactor^2*C*N^(2*delta)*m.E := by have := m.hE; positivity
  have hdiam := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 340+192*m.Lside by have := m.hLside; positivity)
  have hrem0 := m.reverse_nonneg m.D0_pos.le
  have hrem : 0 ≤ (244+192*m.Lside)*m.groupStrength*
      (∫r in Ioo g.a g.b,deriv m.alpha.val.val r)*m.reverse m.D0 := by
    have := m.hLside
    have := m.groupStrength_pos
    positivity
  have hdiam0 : 0 ≤ 96*m.groupStrength*
      (∫r in Ioo g.a g.b,deriv m.alpha.val.val r)*m.D0^2 := by
    have := m.groupStrength_pos
    positivity
  have hc := hrestore m.P m.y m.bandMass m.groupStrength m.E m.P_pos.le
    (by simpa only [one_mul,hNeq] using data.P_le_N) m.hy.le (hNeq ▸ data.y_upper)
    m.hbandMass.le data.mass_upper m.groupStrength_pos.le (hstrengthL.trans data.lam_le_one)
    (hNeq ▸ data.E_lower)
  have hbin : 0 ≤ ((Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3) := by have := m.P_pos; positivity
  have hcutterm : 0 ≤ m.groupStrength*N^(-Ccut) := by have := m.groupStrength_pos; positivity
  have hc' : 48*m.groupStrength*N^(-Ccut) ≤ m.E := by nlinarith
  simp only [hNeq,hdeq,hQeq] at hr hdiam hb
  have ht' := mul_le_mul_of_nonneg_right ht m.hE.le
  simp only [Real.rpow_zero,mul_one] at h3pow
  have hp25 := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN (show 2*delta ≤ 5*delta by linarith)) m.hE.le
  have hp15 := mul_le_mul_of_nonneg_right (Real.one_le_rpow hN (show 0 ≤ 5*delta by linarith)) m.hE.le
  have hsum := mul_le_mul_of_nonneg_right h3pow (show 0 ≤ N^(5*delta)*m.E by have := m.hE; positivity)
  have he : N^delta*(N^(5*delta)*m.E)=N^(6*delta)*m.E := by
    rw [←mul_assoc,←Real.rpow_add hNp]
    congr 2
    ring
  rw [he] at hsum
  dsimp [F] at hmain
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
