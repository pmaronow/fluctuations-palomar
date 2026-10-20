module

public import ComparisonActualHighOnlyConditionalInnerOrdinaryError
public import ComparisonActualHighOnlyConditionalOuterOrdinaryError

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

theorem eventually_actual_conditional_canonical_ordinary_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ)
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀(P:a.Potential),
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      ∀(F:Finset (ordConnectedSection P.negativeSet)) (A:Set ℝ) (v:ℝ),
      0 < v → v ≤ 1 → a.data.s < v/2 → a.data.U ≤ v →
      (∫u in 0..1,(P.canonicalOrdinarySupport F A v).indicator (fun _=>1)
        (a.R u)*a.comparisonErrorDensity u) ≤ a.data.N^(7*delta)*a.data.E := by
  let Cv:=max 2 (max (4*cu*Az) (2*cu*(Az+1)))
  have hCv1:1 ≤ Cv:=(by norm_num : (1:ℝ) ≤ 2).trans (le_max_left _ _)
  have hCvO:4*cu*Az ≤ Cv:=(le_max_left _ _).trans (le_max_right _ _)
  have HI:=eventually_actual_conditional_inner_ordinary_error_high_only ell hell Bclock Cv
    (D:=D) (zero_le_one.trans hCv1) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  have HO:=eventually_actual_conditional_outer_ordinary_error_high_only ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  filter_upwards [HI,HO] with n hnI hnO
  intro a hs hsxs hd1 hxs hy P hclock F A v hv hv1 hstart hUv
  by_cases hinner:v ≤ Cv*a.xs
  · exact hnI a hs hsxs hd1 hxs hy P hclock F A v hv hv1 hstart hUv hinner
  · have hgt:Cv*a.xs < v:=lt_of_not_ge hinner
    have hxv:a.xs ≤ v:=by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hCv1 a.hxs.le).trans hgt.le
    have houter:4*cu*Az*a.xs ≤ v:=(mul_le_mul_of_nonneg_right hCvO a.hxs.le).trans hgt.le
    exact (hnO a hs hsxs hd1 hxs hy P hclock F A v hv hv1 hUv hstart hxv houter).trans
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le
        (show 1 ≤ a.data.N by exact_mod_cast Nat.succ_pos n)
        (by linarith : 4*delta ≤ 7*delta)) a.data.hE.le)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
