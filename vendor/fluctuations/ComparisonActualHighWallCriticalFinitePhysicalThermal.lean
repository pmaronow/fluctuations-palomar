module

public import ComparisonActualHighWallCriticalThermalCount
public import ComparisonActualHighWallCriticalBroadSliceSource
public import ComparisonActualHighWallCriticalBroadNumerics
public import ComparisonActualHighWallOrdinarySaving

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_actual_high_wall_critical_finite_cap_thermal_rate
    {c C : ℝ} (hc : 0 < c) (hC : c < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock),
      a.xs=a.data.d → comparisonSmallMass a.data.N a.data.E≤c*a.data.d →
      32*a.data.s<c*a.data.d → 2*a.data.N^(-(10:ℝ))<comparisonSmallMass a.data.N a.data.E →
      1≤Real.log a.data.N →
      ∀ (P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet))
        (A : Set ℝ),MeasurableSet A → A⊆Ioo a.data.rmin 1 →
        (∀r∈A,c*a.data.d≤a.alpha.val.val r ∧ a.alpha.val.val r≤C*a.data.d) →
      (∫u in 0..1,(A∩((⋃i : F,Ioo (P.capFamily F i).left (P.capFamily F i).right)∪
        P.contactSet)).indicator (fun _=>1) (a.shiftedNativeModel.R u)*
        a.shiftedNativeModel.thermal u) ≤
        10*C*a.data.N^(-actualMassSavingExponent m delta)*a.data.d^3*
          (Nat.ceil (Real.log (1/comparisonSmallMass a.data.N a.data.E)/Real.log 2)+1)+
        (∫u in 0..min (8*a.criticalMassCoverBase) 1,a.shiftedNativeModel.thermal u) := by
  let eta:=actualMassSavingExponent m delta
  have hCo:0<C:=hc.trans hC
  obtain ⟨ellO,hellO,QO,hQO,HOrd⟩:=
    eventually_actual_high_wall_ordinary_group_polynomial_bound (Bclock:=Bclock) 16 (c/16)
      (by norm_num) (by positivity) hm hdelta hroom hcl hcu hAz hC0 hCt hD
  obtain ⟨QB,hQB,HBroad⟩:=eventually_actual_critical_broad_slice_thermal
    (D:=D) (Bclock:=Bclock) 3 (by norm_num) hm hdelta hroom hcl hcu hAz hC0 hCt
  have HNumeric:=eventually_actual_high_wall_critical_broad_budget_polynomial_le
    (cu:=cu) (D:=D) (Bclock:=Bclock) 3 (by norm_num) QB hQB hm hdelta hcl hAz hCt hC0
      (show 0<c/4 by positivity) (show 0≤2*C by positivity)
  filter_upwards [HOrd,HBroad,HNumeric] with n hnOrd hnBroad hnNum
  intro a hfixed hU hstart hcutU hlog P F A hA hAD hscale
  let cF:=P.capFamily F
  let q:ℝ:=Nat.ceil (Real.log (1/comparisonSmallMass a.data.N a.data.E)/Real.log 2)+1
  let O:=C*a.data.N^(-eta)*a.data.d^3
  let B:=2*C*a.data.N^(-eta)*a.data.d^3
  have hq:0≤q:=by dsimp [q];positivity
  have hO:0≤O:=by
    dsimp only [O]
    exact mul_nonneg (mul_nonneg hCo.le (Real.rpow_nonneg a.data.hN.le _))
      (pow_nonneg a.data.hd.le 3)
  have hB:0≤B:=by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hCo.le)
      (Real.rpow_nonneg a.data.hN.le _)) (pow_nonneg a.data.hd.le 3)
  have hcut : 0<a.data.N^(-(10:ℝ)):=Real.rpow_pos_of_pos a.data.hN _
  have hlogcut : Real.log (1/a.data.N^(-(10:ℝ)))≤10*Real.log a.data.N:=by
    rw [one_div,Real.log_inv,Real.log_rpow a.data.hN]
    ring_nf
    exact le_refl _
  have hordinary (j : CriticalCompleteMassDyad a (c*a.data.d) (C*a.data.d)) :
      (∫u in 0..1,(P.ordinaryGroup cF A 16 j.val).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)≤O:=by
    let v:=comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j.val.val:ℕ)
    have hv:0<v:=(comparison_mass_dyadic_scale a.data.hU j.val).1
    have hv1:v≤1:=(comparison_mass_dyadic_scale a.data.hU j.val).2.2
    have hvlo:(c/16)*a.data.d≤v:=by dsimp only [v];linarith [j.property.1]
    have hvhi:v≤C*a.data.d:=j.property.2
    have hs:a.data.s<v/2:=by linarith [j.property.1,hstart]
    have HH:=hnOrd a hfixed.le P F A j.val hv1 hvlo hs
    have hden:0<a.xs^4*v/a.data.d^2:=
      div_pos (mul_pos (pow_pos a.hxs 4) hv) (sq_pos_of_pos a.data.hd)
    have Hprice:=(div_le_iff₀ hden).mp HH
    have hEq:a.xs^4*v/a.data.d^2=a.data.d^2*v:=by rw [hfixed];field_simp
    rw [hEq] at Hprice
    have Hscale:=mul_le_mul_of_nonneg_left hvhi
      (mul_nonneg (Real.rpow_nonneg a.data.hN.le (-eta)) (sq_nonneg a.data.d))
    apply Hprice.trans
    dsimp only [O,eta]
    nlinarith only [Hscale]
  have hbroad (p : CriticalRelevantBroadSlice cF A) :
      (∫u in 0..1,(actualCriticalBroadSlice cF p.val).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)≤B:=by
    let f:=actualCriticalBroadCapSampler cF p.val.1
    let v:=f.scale p.val.2
    let width:=∫r in f.slice p.val.2,deriv a.alpha.val.val r
    have hv:0<v:=(criticalMassCoverBase_pos (a:=a)).trans_le (f.geometry p.val.2).1
    have hw:=f.width_bounds p.val.2
    have hv1:v≤1:=hw.1.trans hw.2.2
    have hscaleB:=critical_relevant_broad_slice_scale_bounds cF A hscale p
    have hvlo:(c/4)*a.data.d≤v:=by dsimp only [v];linarith [hscaleB.1]
    have hvhi:v≤(2*C)*a.data.d:=by dsimp only [v];linarith [hscaleB.2]
    have hcontacts:=P.capFamily_contacts F p.val.1.val
    have HS:=hnBroad a P (cF p.val.1.val) f p.val.2
      (10*Real.log a.data.N) (a.data.N^(-(10:ℝ))) hcontacts
      (by linarith) hcut hcutU hlogcut
    have HN:=hnNum a hfixed v width hv hv1 hvlo hvhi hw.1 hw.2.1 hw.2.2
    have hden:0<a.data.d^2*v:=mul_pos (sq_pos_of_pos a.data.hd) hv
    have Hprice:=(div_le_iff₀ hden).mp HN
    have Hsize:=mul_le_mul_of_nonneg_left hvhi
      (mul_nonneg (Real.rpow_nonneg a.data.hN.le (-eta)) (sq_nonneg a.data.d))
    apply HS.trans (Hprice.trans _)
    dsimp only [B,eta]
    nlinarith only [Hsize]
  have Hfinite:=P.critical_finite_cap_thermal_le_budget cF A hA hAD hU hstart
    hscale hordinary hbroad
  have HcardO:=critical_complete_mass_dyad_card_le_log (a:=a) (c*a.data.d) (C*a.data.d)
  have HcardB:=critical_broad_slice_card_le_original_mass_log cF
    (P.capFamily_disjoint F) A
  have Hord:=mul_le_mul_of_nonneg_left
    (show (Fintype.card (CriticalCompleteMassDyad a (c*a.data.d) (C*a.data.d)):ℝ)≤q by
      dsimp only [q];exact_mod_cast HcardO)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) hO)
  have Hbroad:=mul_le_mul_of_nonneg_left
    (show (Fintype.card (CriticalRelevantBroadSlice cF A):ℝ)≤4*q by
      dsimp only [q];exact_mod_cast HcardB)
    hB
  have Htotal:=add_le_add (add_le_add Hord Hbroad)
    (le_refl (∫u in 0..min (8*a.criticalMassCoverBase) 1,a.shiftedNativeModel.thermal u))
  apply Hfinite.trans
  convert Htotal using 1
  dsimp only [O,B,q,eta,cF]
  ring

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
