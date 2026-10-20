module

public import ComparisonActualHighWallUniformWholeThermal
public import ComparisonActualHighWallUniformOuterThermalAlong
public import ComparisonActualHighWallUniformFloorThermal
public import ComparisonActualHighWallWholeThermalCore

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_uniform_whole_thermal_dyads_along
    {m delta cl cu Az C0 Ct D Bclock c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hD : 0 < D) (hc : 0 < c) (hcout : cu*Az < c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxsd : ∀n,(M n).xs ≤ (M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∀ᶠn in atTop,∀v : ℝ,c*(M n).data.d ≤ v → 2*v ≤ 1 →
      (∫u in Ioo v (2*v),orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2) ≤
        (M n).data.N^(-(actualMassSavingExponent m delta/2))*(M n).data.d^2*v := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  have HO:=eventually_actual_high_wall_uniform_outer_cap_contact_thermal_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hD hcout (by linarith : c < 2*c)
    dim hdim M hxsd hdlim hsRatio
  have HF:=eventually_actual_high_wall_uniform_outer_floor_thermal
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hc hcout
  have HR:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=1/2) (q:=-(5*eta/8)) (r:=-(eta/2))
      (by norm_num) (by linarith))
  have HS:=hsRatio.eventually (eventually_le_nhds hc)
  filter_upwards [HO,(hdim.eventually HF),HR,HS] with n hnO hnF hnR hnS
  intro v hvd hv1
  let a:=M n
  have hv : 0 < v:=(mul_pos hc a.data.hd).trans_le hvd
  have hsv : a.data.s ≤ v:=by
    have H:=(div_le_iff₀ a.data.hd).mp hnS
    exact H.trans (by simpa only [mul_comm] using hvd)
  obtain ⟨P⟩:=a.exists_potential
  let W:=v/c
  have hdW : a.data.d ≤ W:=(le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvd)
  have He1 : c*W=v:=by dsimp only [W];field_simp
  have He2 : (2*c)*W=2*v:=by dsimp only [W];field_simp
  have hHi : (2*c)*W ≤ 1:=by rw [He2];exact hv1
  have Hcap:=hnO W hdW hHi P
  rw [He1,He2,show 2*v-v=v by ring] at Hcap
  have Hcoef : a.data.N^(-(5*eta/8)) ≤ (1/2)*a.data.N^(-(eta/2)):=by
    simpa only [Function.comp_apply,one_mul,ActualHighWallData.N,a] using hnR
  have Hhalf:=mul_le_mul_of_nonneg_right Hcoef (mul_nonneg (sq_nonneg a.data.d) hv.le)
  have HcapHalf :
      (∫u in Ioo v (2*v),(P.negativeSet∪P.contactSet).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) ≤
      (1/2)*a.data.N^(-(eta/2))*a.data.d^2*v := by
    exact Hcap.trans (by simpa only [eta,a,mul_assoc] using Hhalf)
  have Hfloor:=hnF a (hxsd n) P v hvd hsv hv1
  have hlohi : v ≤ 2*v:=by linarith only [hv]
  change (∫u in Ioo v (2*v),a.shiftedNativeModel.thermal u) ≤ _
  rw [P.mass_thermal_slab_decomposition hsv hlohi hv1]
  exact (add_le_add Hfloor HcapHalf).trans_eq (by dsimp only [eta,a];ring)

end OAI.SKFluctuations.LaplaceWindowFormalization
