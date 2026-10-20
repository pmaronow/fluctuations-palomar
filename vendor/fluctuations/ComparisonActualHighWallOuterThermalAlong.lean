module

public import ComparisonActualHighWallOuterThermal
public import ComparisonActualHighWallStarBandParametersAlong
public import ComparisonActualHighWallOrdinarySaving
public import ComparisonNativeActualMassBudgetRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 26000000
attribute [local instance] Classical.propDecidable

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

end ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_outer_cap_contact_thermal_along
    {m delta cl cu Az C0 Ct D Bclock A B : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) (hD : 0<D)
    (hA : cu*Az<A) (hAB : A<B)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsd : ∀n,(M n).xs ≤ (M n).data.d) (hdW : ∀n,(M n).data.d ≤ W n)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0)) :
    ∀ᶠn : ℕ in atTop,∀P : (M n).Potential,
      (∫u in Ioo (A*W n) (B*W n),(P.negativeSet∪P.contactSet).indicator (fun _=>1)
        ((M n).shiftedNativeModel.R u)*(M n).shiftedNativeModel.thermal u) ≤
          (M n).data.N^(-(5*actualMassSavingExponent m delta/8))*(W n)^2*(B*W n-A*W n) := by
  let eta:=actualMassSavingExponent m delta
  let K:=max 16 (4*cu/cl)
  let c:=cl*A/(4*cu)
  let Ccount:=actualHighWallMassCountConstant D
  let Ctotal:=Ccount*B/(B-A)
  have heta : 0<eta:=actualMassSavingExponent_pos hm hdelta
  have hA0 : 0<A:=(mul_nonneg hcu.le hAz).trans_lt hA
  have hB0 : 0<B:=hA0.trans hAB
  have hc : 0<c:=by dsimp only [c];positivity
  have hK16 : 16 ≤ K:=le_max_left _ _
  have hK4 : (4:ℝ) ≤ K:=(by norm_num : (4:ℝ) ≤ 16).trans hK16
  have hKcap : 4*cu/cl ≤ K:=le_max_right _ _
  have hxsW n : (M n).xs ≤ W n:=(hxsd n).trans (hdW n)
  obtain ⟨ell,hell,Q,hQ,Hordinary⟩:=eventually_actual_high_wall_ordinary_group_polynomial_bound
    K c hK16 hc hm hdelta hroom hcl hcu hAz hC0 hCt hD
  have Hparameters:=eventually_actual_high_wall_star_band_parameters_along hm hdelta hcl hcu hAz hC0 hA
    dim hdim M W hxsW hsRatio
  have Hdecay:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (native_mass_log_power_decay (q:=eta) (s:=5*eta/8) (by linarith) 1 Ctotal)
  have Hlog:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  have Hhi:=(hWlim.const_mul B).eventually (eventually_le_nhds (show B*(0:ℝ)<1 by simp))
  filter_upwards [(hdim.eventually Hordinary),Hparameters,Hdecay,Hlog,Hhi] with n hnOrd hnParam hnDecay hnLog hnHi
  intro P
  let a:=M n
  let model:=a.shiftedNativeModel
  let lo:=A*W n
  let hi:=B*W n
  let slab:=model.massSlice lo hi
  have hW : 0<W n:=a.data.hd.trans_le (hdW n)
  have hxp:=a.hxs
  have hdp:=a.data.hd
  have hlohi : lo ≤ hi:=mul_le_mul_of_nonneg_right hAB.le hW.le
  have hhi1 : hi ≤ 1:=hnHi
  have hhi0 : 0 ≤ hi:=(mul_pos hB0 hW).le
  obtain ⟨hslo,hgap,htravelLow,htravelGap,hU,hstart4,_⟩:=hnParam
  have hloI : lo∈Icc a.data.s 1:=⟨hslo.le,hlohi.trans hhi1⟩
  have hhiI : hi∈Icc a.data.s 1:=⟨hslo.le.trans hlohi,hhi1⟩
  have hstart : 2*a.data.s ≤ (cl/(4*cu))*lo:=by linarith [a.data.hs.1]
  have hAD : slab⊆Ioo a.data.rmin 1:=fun r hr=>
    ⟨(model.R_bounds lo).1.trans_lt hr.1,hr.2.trans_le (model.R_bounds hi).2⟩
  have hscale : ∀r∈slab,lo ≤ a.alpha.val.val r ∧ a.alpha.val.val r ≤ hi := by
    intro r hr
    have HL:=a.alpha.val.property.2 hr.1.le
    have HR:=a.alpha.val.property.2 hr.2.le
    rw [model.R_spec hloI] at HL
    rw [model.R_spec hhiI] at HR
    exact ⟨HL,HR⟩
  have hN : 1 ≤ a.data.N:=by exact_mod_cast Nat.succ_pos (dim n)
  have hlog : 1 ≤ Real.log a.data.N:=hnLog
  have Hthermal:=P.regular_cap_contact_thermal_le_scaled_groups slab measurableSet_Ioo hAD
    hcl hcu hAz hgap hhi0 htravelLow htravelGap hU hstart hK4 hKcap hscale hN hlog (eta:=eta) (by
      intro F j
      let v:=comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j.val:ℕ)
      have hvhi : v ≤ hi:=j.property.2
      have hvlo : c*W n ≤ v:=by
        convert j.property.1 using 1
        dsimp only [c,lo]
        ring
      have hvd : c*a.data.d ≤ v:=(mul_le_mul_of_nonneg_left (hdW n) hc.le).trans hvlo
      have hs : a.data.s<v/2:=by
        have HV : 4*a.data.s ≤ v:=hstart4.trans (by
          convert hvlo using 1
          dsimp only [c,lo]
          ring)
        linarith [a.data.hs.1]
      exact hnOrd a (hxsd n) P F slab j.val (hvhi.trans hhi1) hvd hs)
  rw [P.cap_contact_massSlice_integral hloI hhiI hlohi,
    intervalIntegral.integral_of_le hlohi,integral_Ioc_eq_integral_Ioo] at Hthermal
  have Hxs : a.xs^4/a.data.d^2 ≤ (W n)^2 := by
    calc
      _ ≤ a.data.d^4/a.data.d^2:=div_le_div_of_nonneg_right
        (pow_le_pow_left₀ a.hxs.le (hxsd n) 4) (sq_nonneg _)
      _=a.data.d^2:=by field_simp
      _ ≤ _:=pow_le_pow_left₀ a.data.hd.le (hdW n) 2
  have Hden : a.xs^4*hi/a.data.d^2 ≤ (W n)^2*hi := by
    have HE : a.xs^4*hi/a.data.d^2=(a.xs^4/a.data.d^2)*hi:=by ring
    rw [HE]
    exact mul_le_mul_of_nonneg_right Hxs hhi0
  have Hcount0 : 0 ≤ Ccount*Real.log a.data.N:=
    mul_nonneg (actualHighWallMassCountConstant_pos D).le (by linarith)
  have Hbudget : a.data.N^(-eta)*(a.xs^4*hi/a.data.d^2)*(Ccount*Real.log a.data.N) ≤
      a.data.N^(-eta)*((W n)^2*hi)*(Ccount*Real.log a.data.N):=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left Hden (Real.rpow_nonneg a.data.hN.le _)) Hcount0
  have Hdec : Ctotal*Real.log a.data.N*a.data.N^(-eta) ≤ a.data.N^(-(5*eta/8)):=by
    simpa only [Function.comp_apply,ActualHighWallData.N,pow_one] using hnDecay
  have Hspan0 : 0 ≤ (W n)^2*(hi-lo):=mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hlohi)
  calc
    _ ≤ a.data.N^(-eta)*((W n)^2*hi)*(Ccount*Real.log a.data.N):=Hthermal.trans Hbudget
    _=(Ctotal*Real.log a.data.N*a.data.N^(-eta))*((W n)^2*(hi-lo)):=by
      dsimp only [Ctotal,hi,lo]
      field_simp [sub_ne_zero.mpr hAB.ne']
    _ ≤ a.data.N^(-(5*eta/8))*((W n)^2*(hi-lo)):=mul_le_mul_of_nonneg_right Hdec Hspan0
    _=a.data.N^(-(5*eta/8))*(W n)^2*(B*W n-A*W n):=by ring

end OAI.SKFluctuations.LaplaceWindowFormalization
