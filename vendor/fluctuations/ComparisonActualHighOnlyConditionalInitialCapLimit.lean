module

public import ComparisonActualHighOnlyConditionalInitialCapError
public import ComparisonActualHighOnlyConditionalThinMassError

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 22000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem error_interval_left_tendsto_high_only
    (a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {lo hi:ℝ} (hlo:lo∈Icc (0:ℝ) hi) (hhi:hi ≤ 1)
    (u:ℕ→ℝ) (hu:∀j,u j∈Icc (0:ℝ) hi) (hlim:Tendsto u atTop (𝓝 lo)) :
    Tendsto (fun j=>∫r in u j..hi,a.comparisonErrorDensity r) atTop
      (𝓝 (∫r in lo..hi,a.comparisonErrorDensity r)) := by
  have hhi0:0 ≤ hi:=hlo.1.trans hlo.2
  have hInt:IntegrableOn a.comparisonErrorDensity (uIcc (0:ℝ) hi):=by
    rw [uIcc_of_le hhi0]
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      a.comparisonErrorDensity_intervalIntegrable).mono_set (Icc_subset_Icc le_rfl hhi)
  have Hcont:ContinuousOn (fun t=>∫r in t..hi,a.comparisonErrorDensity r) (Icc (0:ℝ) hi):=by
    simpa only [uIcc_of_le hhi0] using intervalIntegral.continuousOn_primitive_interval_left hInt
  exact (Hcont lo hlo).tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hlim,Eventually.of_forall hu⟩)

theorem eventually_actual_conditional_small_initial_cap_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ)
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs) (hUs:a.data.U ≤ a.data.s),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀(P:a.Potential) (cap:ShiftedCapInterval a P),
      cap.left=0 → (P.H cap.right=0 ∨ cap.right=1) →
      a.alpha.val.val cap.right ≤ 16*a.data.s →
      (∫u in a.data.s..a.alpha.val.val cap.right,a.comparisonErrorDensity u) ≤
        a.data.N^(6*delta)*a.data.E := by
  have Hcrop:=eventually_actual_conditional_initial_cap_crop_error_high_only ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  have Hthin:=eventually_actual_conditional_thin_mass_error_high_only Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hcut:=(tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (comparison_log_loss_eventually (C:=8) (p:=0) (by norm_num) (by norm_num : (0:ℝ) < 9))
  filter_upwards [Hcrop,Hthin,Hcut,eventually_actual_minimum_physical_scalar_data_high_only hm hC0]
    with n hnCrop hnThin hnCut hnScalar
  intro a hs hsxs hUs hd1 hxs hy P cap hleft hend hband
  have hscalar:=hnScalar a hd1
  have hN:1 ≤ a.data.N:=by exact_mod_cast Nat.succ_pos n
  have hspos:0 < a.data.s:=a.data.hU.trans_le hUs
  have hrpos:0 < cap.right:=by have H:=cap.hlt;rw [hleft] at H;exact H
  have hαr:=a.alpha.val.property.1 cap.right
  have hsV:a.data.s ≤ a.alpha.val.val cap.right:=by
    rw [←a.alpha.property.1];exact a.alpha.val.property.2 hrpos.le
  by_cases hwidth:a.alpha.val.val cap.right-a.data.s ≤ a.data.U
  · have HE:=hnThin a hd1 hs hsxs hxs a.data.s (a.alpha.val.val cap.right)
      ⟨a.data.hs.1,a.data.hs1⟩ hαr hsV hwidth
      (by linarith only [hwidth,hsxs,hscalar.2.2.2.2.2.1])
    exact HE.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith : 3*delta ≤ 6*delta)) a.data.hE.le)
  · have hwpos:0 < a.alpha.val.val cap.right-a.data.s:=a.data.hU.trans (lt_of_not_ge hwidth)
    let l:=fun j:ℕ=>cap.right/((j+2:ℕ):ℝ)
    have hlpos j:0 < l j:=by dsimp [l];positivity
    have hlr j:l j < cap.right:=by
      apply (div_lt_iff₀ (by positivity : (0:ℝ) < ((j+2:ℕ):ℝ))).mpr
      have H:(1:ℝ) < ((j+2:ℕ):ℝ):=by exact_mod_cast (show 1 < j+2 by omega)
      nlinarith only [H,hrpos]
    have hlim:Tendsto l atTop (𝓝 0):=by
      have H:=(tendsto_inv_atTop_zero : Tendsto (fun x:ℝ=>x⁻¹) atTop (𝓝 0)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
      simpa only [l,div_eq_mul_inv,mul_zero,Function.comp_apply] using H.const_mul cap.right
    have hαcont:ContinuousOn a.alpha.val.val (Icc (0:ℝ) 1):=
      (inverseIntegralConstraints_lipschitz a.data.hm a.data.hM a.alpha.property).continuousOn
    have hαlim:Tendsto (fun j=>a.alpha.val.val (l j)) atTop (𝓝 a.data.s):=by
      rw [←a.alpha.property.1]
      exact (hαcont 0 ⟨le_rfl,zero_le_one⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hlim,Eventually.of_forall
          (fun j=>⟨(hlpos j).le,(hlr j).le.trans cap.hright⟩)⟩)
    have Hhalf:∀ᶠj:ℕ in atTop,a.alpha.val.val (l j) ≤
        (a.alpha.val.val cap.right+a.data.s)/2:=
      hαlim.eventually (eventually_le_nhds (by linarith only [hwpos]))
    have hcut4:4*a.data.N^(-(10:ℝ)) < a.data.U:=by
      have HH:8 ≤ a.data.N^(9:ℝ):=by
        simpa only [Function.comp_apply,Real.rpow_zero,mul_one] using hnCut
      have HM:=mul_le_mul_of_nonneg_right HH (Real.rpow_nonneg a.data.hN.le (-(10:ℝ)))
      have He:a.data.N^(9:ℝ)*a.data.N^(-(10:ℝ))=1/a.data.N:=by
        rw [←Real.rpow_add a.data.hN]
        norm_num only [show (9:ℝ)+-(10:ℝ)= -1 by norm_num,Real.rpow_neg_one]
        simp only [one_div]
      rw [He] at HM
      have Hpos:=Real.rpow_pos_of_pos a.data.hN (-(10:ℝ))
      exact lt_of_lt_of_le (by linarith only [HM,Hpos]) hscalar.2.2.2.1
    apply le_of_tendsto (a.error_interval_left_tendsto_high_only ⟨a.data.hs.1,hsV⟩ hαr.2
      (fun j=>a.alpha.val.val (l j)) (fun j=>⟨(a.alpha.val.property.1 _).1,
        a.alpha.val.property.2 (hlr j).le⟩) hαlim)
    filter_upwards [Hhalf] with j hj
    exact hnCrop a hs hsxs hUs hd1 hxs hy P cap (l j) hleft hend hband
      (hlpos j) (hlr j) (by linarith only [hj])
      (by linarith only [hj,hcut4,lt_of_not_ge hwidth])

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
