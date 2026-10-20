module

public import ComparisonActualHighOnlyConditionalInitialCapError
public import ComparisonActualHighOnlyConditionalBroadSourceBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 20000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum

theorem eventually_actual_conditional_inner_broad_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock Cv:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hCv:0 ≤ Cv) (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀(P:a.Potential) (cap:ShiftedCapInterval a P) (l z v:ℝ),
      (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1) →
      0 < l → l < z → cap.left ≤ l → z ≤ cap.right →
      0 < v → v ≤ 1 → a.data.U ≤ v → v ≤ Cv*a.xs →
      v/2 ≤ a.alpha.val.val l → a.alpha.val.val z ≤ min (4*v) 1 →
      v ≤ a.alpha.val.val z-a.alpha.val.val l →
      (∫u in a.alpha.val.val l..a.alpha.val.val z,a.comparisonErrorDensity u) ≤
        a.data.N^(6*delta)*a.data.E := by
  obtain ⟨Q,hQ,HS⟩:=eventually_actual_high_only_broad_mass_budget_without_wall_scale ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have HP:=eventually_actual_conditional_broad_budget_price_high_only (cu:=cu) (D:=D) (Bclock:=Bclock) (Ct:=Ct)
    ell hell Q Cv hQ hCv hm hdelta hcl hAz hC0 horder
  have Hcut:=(tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (comparison_log_loss_eventually (C:=8) (p:=0) (by norm_num) (by norm_num : (0:ℝ) < 9))
  have Hlog:=(tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  filter_upwards [HS,HP,Hcut,Hlog,eventually_actual_minimum_physical_scalar_data_high_only hm hC0]
    with n hnS hnP hnCut hnLog hnScalar
  intro a hs hsxs hd1 hxs hy P cap l z v hcontacts hl0 hlz hclL hzcap hv hv1 hUv hvA hRho hupper hwidth
  have hlog:1 ≤ Real.log a.data.N:=by simpa only [Function.comp_apply] using hnLog
  have hscalar:=hnScalar a hd1
  have hαl:=a.alpha.val.property.1 l
  have hαz:=a.alpha.val.property.1 z
  have hm:=a.inverse_slice_mass hl0.le hlz.le (hzcap.trans cap.hright)
  have hcutU:2*a.data.N^(-(10:ℝ)) < a.data.U:=by
    have HH:8 ≤ a.data.N^(9:ℝ):=by simpa only [Function.comp_apply,Real.rpow_zero,mul_one] using hnCut
    have HM:=mul_le_mul_of_nonneg_right HH (Real.rpow_nonneg a.data.hN.le (-(10:ℝ)))
    have He:a.data.N^(9:ℝ)*a.data.N^(-(10:ℝ))=1/a.data.N:=by
      rw [←Real.rpow_add a.data.hN]
      norm_num only [show (9:ℝ)+-(10:ℝ)= -1 by norm_num,Real.rpow_neg_one]
      simp only [one_div]
    rw [He] at HM
    have Hpos:=Real.rpow_pos_of_pos a.data.hN (-(10:ℝ))
    exact lt_of_lt_of_le (by linarith only [HM,Hpos]) hscalar.2.2.2.1
  have HT:=hnS a hs hsxs P cap l z v (10*Real.log a.data.N) (a.data.N^(-(10:ℝ)))
    hcontacts hl0 hlz hclL hzcap hv hv1 hUv hRho hupper (by rw [hm];exact hwidth)
    (by linarith only [hlog]) (Real.rpow_pos_of_pos a.data.hN _) hcutU
    (comparison_physical_cutoff_log (C:=10) a.data.hN).2.le
  have hsα:a.data.s ≤ a.alpha.val.val l:=by rw [←a.alpha.property.1];exact a.alpha.val.property.2 hl0.le
  have hsub:=a.shiftedNativeModel.mass_radius_cell_substitution a.shiftedNativeModel.thermal
    (show a.alpha.val.val l∈Icc a.data.s 1 from ⟨hsα,hαl.2⟩)
    (show a.alpha.val.val z∈Icc a.data.s 1 from ⟨hsα.trans (a.alpha.val.property.2 hlz.le),hαz.2⟩)
    (a.alpha.val.property.2 hlz.le)
  rw [a.shiftedNativeModel.R_inverse ⟨hl0.le,hlz.le.trans (hzcap.trans cap.hright)⟩,
    a.shiftedNativeModel.R_inverse ⟨hl0.le.trans hlz.le,hzcap.trans cap.hright⟩,
    integral_Icc_eq_integral_Ioo] at hsub
  rw [←hsub,hm] at HT
  have HE:=P.cap_mass_error_le_thermal_high_only cap hclL hl0.le hlz.le hzcap
  have hD:a.cavityCapTravel ≤ a.canonicalMassDiameter:=by
    unfold canonicalMassDiameter
    have H:=mul_nonneg (show 0 ≤ 9*Real.log a.data.N-1 by linarith only [hlog]) a.cavityCapTravel_nonneg
    nlinarith only [H]
  have hw0:0 ≤ a.alpha.val.val z-a.alpha.val.val l:=sub_nonneg.mpr (a.alpha.val.property.2 hlz.le)
  have HM:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ a.cavityCapTravel_nonneg hD 2) (show 0 ≤ 16*a.lam by have H:=a.hlam;positivity)) hw0
  have HL:=mul_le_mul_of_nonneg_left HT (show 0 ≤ 3*a.lam by have H:=a.hlam;positivity)
  have HC:=hnP a hd1 hxs hy v (a.alpha.val.val z-a.alpha.val.val l) hv hv1 hUv hvA hw0
    (by linarith only [hupper.trans (min_le_left _ _),hαl.1])
    (by linarith only [hαz.2,hαl.1])
  exact HE.trans ((add_le_add HL HM).trans HC)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
