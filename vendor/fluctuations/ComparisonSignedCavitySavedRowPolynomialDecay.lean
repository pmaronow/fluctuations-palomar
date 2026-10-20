module

public import ComparisonSignedCavityActualSavedPowerRow
public import ComparisonNativeActualMassBudgetRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ClockTree

theorem eventually_native_saved_row_polynomial_decay {eta : ℝ} (heta : 0 < eta)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠn : ℕ in atTop,C*Real.log ((n+1:ℕ):ℝ)*((n:ℝ)^(-eta))^2 ≤ (n:ℝ)^(-eta) := by
  filter_upwards [native_mass_log_power_decay (q:=2*eta) (s:=eta) (by linarith) 1 (2*C),
    eventually_ge_atTop (2:ℕ)] with n hn hn2
  have hN2 : (2:ℝ) ≤ n:=by exact_mod_cast hn2
  have hN : (0:ℝ) < n:=by linarith
  have hlog : Real.log ((n+1:ℕ):ℝ) ≤ 2*Real.log (n:ℝ) := by
    calc
      _ ≤ Real.log ((n:ℝ)^2) := Real.log_le_log (by positivity) (by
        push_cast
        nlinarith)
      _ = _ := by rw [Real.log_pow];norm_num
  have Hpow : ((n:ℝ)^(-eta))^2=(n:ℝ)^(-(2*eta)) := by
    rw [←Real.rpow_mul_natCast hN.le]
    norm_num
    congr 1
    ring
  rw [Hpow]
  apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC)
    (Real.rpow_nonneg hN.le _))
  convert hn using 1
  ring

theorem eventually_actual_minimum_bare_saved_polarized_row_decay
    {eta : ℝ} (heta : 0 < eta) (A : ℝ) (hA : 0 ≤ A)
    (Bclock Temp : ℝ) (hT : 0 ≤ Temp) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
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
            |fullScalarCutGamma p.tree U (retainedStarMixedClock n M.bf M.hf as)
              (p.embed P.live.test.target) p.mark| *
            nativeTargetOffDiagonalProfile T P.live.test.target
              (fun j=>if V ≤ M.R (partitionPoint 0 as j) then
                nativeSavedIncomingScale M.xs W s
                  (M.R (partitionPoint 0 as j)) else 0) p)).sum ≤
            (n:ℝ)^(-eta)*(W*M.xs^2) := by
  obtain ⟨Ci,hCi,HI⟩:=eventually_actual_minimum_bare_saved_incoming_row_bound
    (D:=D) Bclock Temp hT hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_bare_saved_power_row_bound
    (D:=D) Bclock Temp hT hm hdelta hroom hcl hcu hAz hC0 hCt
  have HRi:=eventually_native_saved_row_polynomial_decay heta (A*Ci) (mul_nonneg hA hCi.le)
  have HRp:=eventually_native_saved_row_polynomial_decay heta (A*Cp) (mul_nonneg hA hCp.le)
  filter_upwards [HI,HP,HRi,HRp] with n hnI hnP hnRi hnRp
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hnI M hb hh hxs L us hus hret hmesh,
    hnP M hb hh hxs L us hus hret hmesh] with k hkI hkP
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
