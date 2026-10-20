module

public import ComparisonActualHighWallSavedRadiusRows

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity ClockTree
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem eventually_actual_high_wall_saved_polarized_radius_row_decay
    {eta : ℝ} (heta : 0<eta) (A : ℝ) (hA : 0≤A)
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as)
          (seed : List NativeResourceMark) (depth : ℕ) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed depth T P → i ≤ star → 0<U →
        ∀W V : ℝ,M.xs ≤ W → M.xs ≤ V → V ≤ 1 → M.z ≤ V →
          M.data.wallRadius M.alpha (partitionPoint 0 as star) ≤ V/2 →
        ∀s : ℝ,s=M.xs+partitionPoint 0 as i ∨ s=W →
        A*((n:ℝ)^(-eta))^2*
        ((T.markedAttach 0).map (fun p=>|p.coeff| *
          |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as)
            (p.embed P.live.test.target) p.mark| *
          nativeTargetOffDiagonalProfile T P.live.test.target
            (fun j=>if V ≤ M.data.wallRadius M.alpha (partitionPoint 0 as j) then
              nativeSavedIncomingScale M.xs W s (M.data.wallRadius M.alpha (partitionPoint 0 as j))
              else 0) p)).sum ≤ (n:ℝ)^(-eta)*(W*M.xs^2) := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_high_wall_saved_polarized_radius_row_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have HR:=eventually_native_saved_row_polynomial_decay heta (A*Cg) (mul_nonneg hA hCg.le)
  filter_upwards [HG,HR] with n hn hnR
  intro M hwork us hus
  filter_upwards [hn M hwork us hus] with jGrid hj
  dsimp only at hj ⊢
  intro i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar s hs
  have hW : 0<W:=M.hxs.trans_le hxW
  have H:=mul_le_mul_of_nonneg_left
    (hj i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar s hs)
    (mul_nonneg hA (sq_nonneg ((n:ℝ)^(-eta))))
  apply H.trans
  convert mul_le_mul_of_nonneg_right hnR (show 0≤W*M.xs^2 by positivity) using 1; ring

end OAI.SKFluctuations.LaplaceWindowFormalization
