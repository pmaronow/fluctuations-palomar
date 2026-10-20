module

public import ComparisonSignedCavitySavedRowPolynomialDecay
public import ComparisonSignedCavityInheritedSavedPowerRow
public import ComparisonNativeActualMassBudgetRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ClockTree

theorem eventually_actual_minimum_inherited_saved_polarized_row_decay
    {eta : ℝ} (heta : 0 < eta) (A : ℝ) (hA : 0 ≤ A)
    (Bclock Temp Cf : ℝ) (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as)
          (seed : List NativeResourceMark) (depth : ℕ) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed depth T P → i ≤ star → 0 < U →
        ∀W V : ℝ,M.xs ≤ W → M.xs ≤ V → V ≤ 1 → M.z ≤ V →
          M.R (partitionPoint 0 as star) ≤ V/2 →
        ∀s : ℝ,s=M.xs+partitionPoint 0 as i ∨ s=W →
          A*((n:ℝ)^(-eta))^2*
          ((T.markedAttach 0).map (fun p=>|p.coeff| *
            |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as)
              (p.embed P.live.test.target) p.mark| *
            nativeTargetOffDiagonalProfile T P.live.test.target
              (fun j=>if V ≤ M.R (partitionPoint 0 as j) then
                nativeSavedIncomingScale M.xs W s
                  (M.R (partitionPoint 0 as j)) else 0) p)).sum ≤
            (n:ℝ)^(-eta)*(W*M.xs^2) := by
  obtain ⟨Ci,hCi,HI⟩:=eventually_actual_minimum_inherited_saved_incoming_row_bound
    (D:=D) Bclock Temp Cf hT hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_saved_power_row_bound
    (D:=D) Bclock Temp Cf hT hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HRi:=eventually_native_saved_row_polynomial_decay heta (A*Ci) (mul_nonneg hA hCi.le)
  have HRp:=eventually_native_saved_row_polynomial_decay heta (A*Cp) (mul_nonneg hA hCp.le)
  filter_upwards [HI,HP,HRi,HRp] with n hnI hnP hnRi hnRp
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hnI M hsource hxs L us hus hret hmesh,
    hnP M hsource hxs L us hus hret hmesh] with k hkI hkP
  dsimp only at hkI hkP ⊢
  intro i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar s hs
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hscale : 0 ≤ W*M.xs^2:=by positivity
  rcases hs with hs|hs
  · subst s
    have H:=mul_le_mul_of_nonneg_left
      (hkI i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar)
      (show 0 ≤ A*((n:ℝ)^(-eta))^2 by positivity)
    apply H.trans
    convert mul_le_mul_of_nonneg_right hnRi hscale using 1
    ring
  · subst s
    have H:=mul_le_mul_of_nonneg_left
      (hkP i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar)
      (show 0 ≤ A*((n:ℝ)^(-eta))^2 by positivity)
    apply H.trans
    convert mul_le_mul_of_nonneg_right hnRp hscale using 1
    ring

end OAI.SKFluctuations.LaplaceWindowFormalization
