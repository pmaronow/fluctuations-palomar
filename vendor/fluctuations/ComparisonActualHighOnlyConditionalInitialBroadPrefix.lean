module

public import ComparisonActualHighOnlyConditionalInitialCapLimit
public import ComparisonActualHighOnlyConditionalInnerBroadError

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock:ℝ}

theorem eventually_actual_conditional_initial_broad_prefix_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ)
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs) (hUs:a.data.U ≤ a.data.s),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀(P:a.Potential) (cap:ShiftedCapInterval a P),
      cap.left=0 → (P.H cap.right=0 ∨ cap.right=1) → 4*a.data.s ≤ a.alpha.val.val cap.right →
      (∫u in a.data.s..4*a.data.s,a.comparisonErrorDensity u) ≤ a.data.N^(6*delta)*a.data.E := by
  have HI:=eventually_actual_conditional_inner_broad_error_high_only ell hell Bclock 2
    (D:=D) (by norm_num) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  filter_upwards [HI] with n hn
  intro a hs hsxs hUs hd1 hxs hy P cap hleft hend hright
  have hspos:0 < a.data.s:=a.data.hU.trans_le hUs
  have hmass:4*a.data.s∈Icc a.data.s 1:=⟨by linarith only [hspos],by linarith only [hs]⟩
  let z:=a.R (4*a.data.s)
  have hz1:z ≤ 1:=(a.shiftedNativeModel.R_bounds _).2
  have hαz:a.alpha.val.val z=4*a.data.s:=a.shiftedNativeModel.R_spec hmass
  have hzpos:0 < z:=by
    by_contra H
    have Hz:z=0:=le_antisymm (le_of_not_gt H) (a.shiftedNativeModel.R_bounds _).1
    rw [Hz,a.alpha.property.1] at hαz
    linarith only [hαz,hspos]
  have hzcap:z ≤ cap.right:=by
    calc z ≤ a.R (a.alpha.val.val cap.right):=a.shiftedNativeModel.R_monotone hright
         _=cap.right:=a.shiftedNativeModel.R_inverse ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩
  let l:=fun j:ℕ=>z/((j+2:ℕ):ℝ)
  have hlpos j:0 < l j:=by dsimp [l];positivity
  have hlz j:l j < z:=by
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < ((j+2:ℕ):ℝ))).mpr
    have H:(1:ℝ) < ((j+2:ℕ):ℝ):=by exact_mod_cast (show 1 < j+2 by omega)
    nlinarith only [H,hzpos]
  have hlim:Tendsto l atTop (𝓝 0):=by
    have H:=(tendsto_inv_atTop_zero : Tendsto (fun x:ℝ=>x⁻¹) atTop (𝓝 0)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    simpa only [l,div_eq_mul_inv,mul_zero,Function.comp_apply] using H.const_mul z
  have hαcont:ContinuousOn a.alpha.val.val (Icc (0:ℝ) 1):=
    (inverseIntegralConstraints_lipschitz a.data.hm a.data.hM a.alpha.property).continuousOn
  have hαlim:Tendsto (fun j=>a.alpha.val.val (l j)) atTop (𝓝 a.data.s):=by
    rw [←a.alpha.property.1]
    exact (hαcont 0 ⟨le_rfl,zero_le_one⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hlim,Eventually.of_forall
        (fun j=>⟨(hlpos j).le,(hlz j).le.trans hz1⟩)⟩)
  have Hsmall:∀ᶠj:ℕ in atTop,a.alpha.val.val (l j) ≤ 2*a.data.s:=
    hαlim.eventually (eventually_le_nhds (by linarith only [hspos]))
  apply le_of_tendsto (a.error_interval_left_tendsto_high_only
    (show a.data.s∈Icc (0:ℝ) (4*a.data.s) from ⟨a.data.hs.1,by linarith only [hspos]⟩)
    (show 4*a.data.s ≤ 1 by linarith only [hs]) (fun j=>a.alpha.val.val (l j))
    (fun j=>⟨(a.alpha.val.property.1 _).1,by rw [←hαz];exact a.alpha.val.property.2 (hlz j).le⟩) hαlim)
  filter_upwards [Hsmall] with j hj
  have hαl:a.data.s ≤ a.alpha.val.val (l j):=by rw [←a.alpha.property.1];exact a.alpha.val.property.2 (hlpos j).le
  have H:=hn a hs hsxs hd1 hxs hy P cap (l j) z (2*a.data.s) ⟨Or.inr hleft,hend⟩
    (hlpos j) (hlz j) (by rw [hleft];exact (hlpos j).le) hzcap (by positivity)
    (by linarith only [hs]) (by linarith only [hUs,hspos]) (by linarith only [hsxs])
    (by linarith only [hαl]) (by rw [hαz];exact le_min (by linarith only [hspos]) (by linarith only [hs]))
    (by rw [hαz];linarith only [hj])
  simpa only [hαz] using H

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
