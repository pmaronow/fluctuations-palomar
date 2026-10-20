module

public import ComparisonActualHighOnlyConditionalInnerBroadError
public import ComparisonActualHighOnlyConditionalOuterBroadError

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal
set_option maxHeartbeats 14000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock:ℝ}

theorem eventually_actual_conditional_canonical_broad_crop_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ)
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀(P:a.Potential) (cap:ShiftedCapInterval a P) (l z v:ℝ),
      (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1) →
      0 < l → l < z → cap.left ≤ l → z ≤ cap.right →
      0 < v → v ≤ 1 → a.data.U ≤ v →
      v/2 ≤ a.alpha.val.val l → a.alpha.val.val z ≤ min (4*v) 1 →
      v ≤ a.alpha.val.val z-a.alpha.val.val l →
      (∫u in a.alpha.val.val l..a.alpha.val.val z,a.comparisonErrorDensity u) ≤
        a.data.N^(6*delta)*a.data.E := by
  let Cv:=max 2 (max (4*cu*Az) (2*cu*(Az+1)))
  have hCv2:2 ≤ Cv:=le_max_left _ _
  have hCv1:1 ≤ Cv:=(by norm_num : (1:ℝ) ≤ 2).trans hCv2
  have hCvO:4*cu*Az ≤ Cv:=(le_max_left _ _).trans (le_max_right _ _)
  have hCvC:2*cu*(Az+1) ≤ Cv:=(le_max_right _ _).trans (le_max_right _ _)
  have HI:=eventually_actual_conditional_inner_broad_error_high_only ell hell Bclock Cv
    (D:=D) (zero_le_one.trans hCv1) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  have HO:=eventually_actual_conditional_outer_broad_error_high_only ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  have HT:=(tendsto_add_atTop_nat 1).eventually (eventually_actual_high_only_cap_travel_small
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    (epsilon:=1) hC0 (by linarith : 0 < 3*m+delta) zero_lt_one)
  filter_upwards [HI,HO,HT] with n hnI hnO hnT
  intro a hs hsxs hd1 hxs hy P cap l z v hcontacts hl0 hlz hclL hzcap hv hv1 hUv hRho hupper hwidth
  by_cases hinner:v ≤ Cv*a.xs
  · exact hnI a hs hsxs hd1 hxs hy P cap l z v hcontacts hl0 hlz hclL hzcap hv hv1 hUv hinner hRho hupper hwidth
  · have hgt:Cv*a.xs < v:=lt_of_not_ge hinner
    have hxv:a.xs ≤ v:=by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hCv1 a.hxs.le).trans hgt.le
    have houter:4*cu*Az*a.xs ≤ v:=(mul_le_mul_of_nonneg_right hCvO a.hxs.le).trans hgt.le
    have hvCap:v ≤ a.alpha.val.val cap.right:=by
      have H:=a.alpha.val.property.2 hzcap
      have H0:=(a.alpha.val.property.1 l).1
      linarith only [H,H0,hwidth]
    have hcapOuter:2*cu*(Az+1)*a.xs ≤ a.alpha.val.val cap.right:=
      ((mul_le_mul_of_nonneg_right hCvC a.hxs.le).trans hgt.le).trans hvCap
    have hstart:a.data.s < v/2:=by
      have H:=mul_le_mul_of_nonneg_right hCv2 a.hxs.le
      linarith only [H,hgt,hsxs]
    have htravel:a.cavityCapTravel ≤ a.xs:=by simpa only [one_mul] using (hnT a).1
    exact (hnO a hs hsxs hd1 hxs hy P cap l z v hcontacts htravel hcapOuter hl0 hlz hclL hzcap
      hv hv1 hstart hUv hxv houter hRho hupper hwidth).trans
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le
        (show 1 ≤ a.data.N by exact_mod_cast Nat.succ_pos n)
        (by linarith : 4*delta ≤ 6*delta)) a.data.hE.le)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
