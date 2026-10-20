module

public import ComparisonActualHighOnlyConditionalMassBandCapSource
public import ComparisonActualHighOnlyConditionalWallOrdinaryError

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 30000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.cap_mass_error_le_thermal_high_only
    (P:a.Potential) (cap:ShiftedCapInterval a P) {l z:ℝ}
    (hl:cap.left ≤ l) (hl0:0 ≤ l) (hlz:l ≤ z) (hz:z ≤ cap.right) :
    (∫u in a.alpha.val.val l..a.alpha.val.val z,a.comparisonErrorDensity u) ≤
      3*a.lam*(∫u in a.alpha.val.val l..a.alpha.val.val z,a.shiftedNativeModel.thermal u)+
        16*a.lam*a.cavityCapTravel^2*(a.alpha.val.val z-a.alpha.val.val l) := by
  have hz1:z ≤ 1:=hz.trans cap.hright
  have hl1:l ≤ 1:=hlz.trans hz1
  have hαl:=a.alpha.val.property.1 l
  have hαz:=a.alpha.val.property.1 z
  have hle:a.alpha.val.val l ≤ a.alpha.val.val z:=a.alpha.val.property.2 hlz
  have hsα:a.data.s ≤ a.alpha.val.val l:=by
    rw [←a.alpha.property.1]
    exact a.alpha.val.property.2 hl0
  have hI:Icc (a.alpha.val.val l) (a.alpha.val.val z)⊆Icc (0:ℝ) 1:=
    Icc_subset_Icc hαl.1 hαz.2
  have hiE:=a.comparisonErrorDensity_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hle,uIcc_of_le zero_le_one];exact hI)
  have hiT:IntervalIntegrable a.shiftedNativeModel.thermal volume
      (a.alpha.val.val l) (a.alpha.val.val z):=
    (physicalOrderedThermal_intervalIntegrable n a.bf a.hf a.bf_monotone a.hf_monotone).mono_set
      (by rw [uIcc_of_le hle,uIcc_of_le zero_le_one];exact hI)
  have Hpoint:∀ᵐu∂volume.restrict (Icc (a.alpha.val.val l) (a.alpha.val.val z)),
      a.comparisonErrorDensity u ≤ 3*a.lam*a.shiftedNativeModel.thermal u+16*a.lam*a.cavityCapTravel^2:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae P.all_nonpositive_squared_mismatch_ae_high_mass,
      ae_restrict_of_ae (volume.ae_ne (a.alpha.val.val l)),
      ae_restrict_of_ae (volume.ae_ne (a.alpha.val.val z))] with u hu hm hlu hzu
    have hui:u∈Icc a.data.s 1:=⟨hsα.trans hu.1,hu.2.trans hαz.2⟩
    have hr:a.R u∈Ioo cap.left cap.right:=by
      have H:=a.shiftedNativeModel.massSlice_quantile_mem
        (show a.alpha.val.val l∈Icc a.data.s 1 from ⟨hsα,hαl.2⟩)
        (show a.alpha.val.val z∈Icc a.data.s 1 from ⟨hsα.trans hle,hαz.2⟩) (hI hu)
      have HH:=H.mpr ⟨lt_of_le_of_ne hu.1 hlu.symm,lt_of_le_of_ne hu.2 hzu⟩
      dsimp only [ShiftedNativeBandModel.massSlice] at HH
      rw [a.shiftedNativeModel.R_inverse ⟨hl0,hl1⟩,a.shiftedNativeModel.R_inverse ⟨hl0.trans hlz,hz1⟩] at HH
      exact ⟨hl.trans_lt HH.1,HH.2.trans_le hz⟩
    have H:=hm hui ((cap.negative _ hr).le)
    have hT0:=a.actual_thermal_nonneg_on_unit (hI hu)
    have H1:=mul_le_mul_of_nonneg_left H (a.coefficient_nonneg u)
    have H2:=mul_le_mul_of_nonneg_right (a.coefficient_le_lam u)
      (show 0 ≤ 3*a.shiftedNativeModel.thermal u+16*a.cavityCapTravel^2 by positivity)
    have H3:=mul_le_mul_of_nonneg_right (a.coefficient_le_lam u) hT0
    dsimp only [comparisonErrorDensity,ShiftedNativeBandModel.thermal] at H1 H2 H3 ⊢
    nlinarith only [H1,H2,H3]
  have H:=intervalIntegral.integral_mono_ae_restrict hle hiE
    ((hiT.const_mul (3*a.lam)).add intervalIntegrable_const) Hpoint
  rw [intervalIntegral.integral_add (hiT.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at H
  simpa only [smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using H

end ActualHighOnlyOverlapMinimum
open ActualHighOnlyOverlapMinimum

theorem eventually_actual_conditional_initial_cap_crop_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs) (hUs:a.data.U ≤ a.data.s),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀(P:a.Potential) (cap:ShiftedCapInterval a P) (l:ℝ),
      cap.left=0 → (P.H cap.right=0 ∨ cap.right=1) →
      a.alpha.val.val cap.right ≤ 16*a.data.s →
      0 < l → l < cap.right →
      a.alpha.val.val cap.right-a.data.s ≤ 2*(a.alpha.val.val cap.right-a.alpha.val.val l) →
      2*a.data.N^(-(10:ℝ)) < a.alpha.val.val cap.right-a.alpha.val.val l →
      (∫u in a.alpha.val.val l..a.alpha.val.val cap.right,a.comparisonErrorDensity u) ≤
        a.data.N^(6*delta)*a.data.E := by
  obtain ⟨Q,hQ,HS⟩:=eventually_actual_high_only_mass_band_cap_source_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have HP:=eventually_actual_conditional_broad_budget_price_high_only (cu:=cu) (D:=D) (Bclock:=Bclock) (Ct:=Ct)
    ell hell Q 4 hQ (by norm_num) hm hdelta hcl hAz hC0 horder
  have Hlog:=(tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  filter_upwards [HS,HP,Hlog] with n hnS hnP hnLog
  intro a hs hsxs hUs hd1 hxs hy P cap l hleft hend hband hl0 hlz hhalf hcutWidth
  have hlog:1 ≤ Real.log a.data.N:=by simpa only [Function.comp_apply] using hnLog
  have hspos:0 < a.data.s:=a.data.hU.trans_le hUs
  have hl1:l ≤ 1:=hlz.le.trans cap.hright
  have hαl:a.data.s ≤ a.alpha.val.val l:=by
    rw [←a.alpha.property.1];exact a.alpha.val.property.2 hl0.le
  have hαr:=a.alpha.val.property.1 cap.right
  have hmass:=a.inverse_slice_mass hl0.le hlz.le cap.hright
  have hfull:=a.inverse_slice_mass cap.hleft cap.hlt.le cap.hright
  rw [hleft,a.alpha.property.1] at hfull
  have hDensity:=cap.complete_density_length_le_of_mass_band_high_only hαr (by norm_num : (1:ℝ) ≤ 16)
    (by rw [hleft,a.alpha.property.1];have HU:=a.data.hU;nlinarith only [hband,HU])
  rw [hleft,hfull] at hDensity
  have HD:a.data.M (a.alpha.val.val cap.right)*(cap.right-cap.left) ≤
      512*(∫r in Ioo l cap.right,deriv a.alpha.val.val r):=by
    rw [hmass,hleft];nlinarith only [hDensity,hhalf]
  have hαupper:a.alpha.val.val cap.right ≤ min (16*(4*a.data.s)) 1:=
    le_min (by linarith only [hband,hspos]) hαr.2
  have HT:=hnS a hs hsxs P cap l cap.right (4*a.data.s) (a.alpha.val.val cap.right)
    (10*Real.log a.data.N) (a.data.N^(-(10:ℝ)))
    ⟨Or.inr hleft,hend⟩ hl0 hlz (by rw [hleft];exact hl0.le) le_rfl
    (by positivity) (by linarith only [hs]) (by linarith only [hαl]) hαupper hαr
    (fun r hr=>a.alpha.val.property.2 hr.2.le) HD (by linarith only [hlog])
    (Real.rpow_pos_of_pos a.data.hN _) (by rw [hmass];exact hcutWidth)
    (comparison_physical_cutoff_log (C:=10) a.data.hN).2.le
  have hsub:=a.shiftedNativeModel.mass_radius_cell_substitution a.shiftedNativeModel.thermal
    (show a.alpha.val.val l∈Icc a.data.s 1 from ⟨hαl,(a.alpha.val.property.1 l).2⟩)
    (show a.alpha.val.val cap.right∈Icc a.data.s 1 from
      ⟨hαl.trans (a.alpha.val.property.2 hlz.le),hαr.2⟩) (a.alpha.val.property.2 hlz.le)
  rw [a.shiftedNativeModel.R_inverse ⟨hl0.le,hl1⟩,
    a.shiftedNativeModel.R_inverse ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩,
    integral_Icc_eq_integral_Ioo] at hsub
  rw [←hsub,hmass] at HT
  have HE:=P.cap_mass_error_le_thermal_high_only cap (by rw [hleft];exact hl0.le) hl0.le hlz.le le_rfl
  have hD:a.cavityCapTravel ≤ a.canonicalMassDiameter:=by
    unfold canonicalMassDiameter
    have H:=mul_nonneg (show 0 ≤ 9*Real.log a.data.N-1 by linarith only [hlog]) a.cavityCapTravel_nonneg
    nlinarith only [H]
  have hw0:0 ≤ a.alpha.val.val cap.right-a.alpha.val.val l:=sub_nonneg.mpr (a.alpha.val.property.2 hlz.le)
  have HM:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ a.cavityCapTravel_nonneg hD 2) (show 0 ≤ 16*a.lam by have hl:=a.hlam;positivity)) hw0
  have HL:=mul_le_mul_of_nonneg_left HT (show 0 ≤ 3*a.lam by have hl:=a.hlam;positivity)
  have HC:=hnP a hd1 hxs hy (4*a.data.s) (a.alpha.val.val cap.right-a.alpha.val.val l)
    (by positivity) (by linarith only [hs]) (by linarith only [hUs,hspos])
    (by linarith only [hsxs]) hw0 (by linarith only [hband,hαl,hspos])
    (by linarith only [hαr.2,(a.alpha.val.property.1 l).1])
  exact HE.trans ((add_le_add HL HM).trans HC)

end OAI.SKFluctuations.LaplaceWindowFormalization
