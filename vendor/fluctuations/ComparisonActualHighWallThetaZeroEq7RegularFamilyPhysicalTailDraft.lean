module

public import ComparisonActualHighWallThetaZeroEq7RegularFiniteFamilyRateDraft
public import ComparisonActualHighWallThetaZeroEq7OrdinaryUniformTailDraft
public import ComparisonActualHighWallThetaZeroEq7BroadCapLengthTailDraft
public import ComparisonActualHighWallThetaZeroSmallMassScale
public import ComparisonReverseInterpolationSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable

namespace OriginalQEq7RegularFamilyPhysicalTailDraft

theorem cut_below_mass {N U beta : ℝ}
    (hN : 4 ≤ N) (hbeta : 2 ≤ beta) (hNU : N^(-(1:ℝ)) ≤ U) :
    2*N^(-beta) < U := by
  have hNp : 0 < N := by linarith only [hN]
  have hN1 : 1 ≤ N := by linarith only [hN]
  have hpow : N^(-beta) ≤ N^(-(2:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hbeta])
  have he2 : N^(-(2:ℝ)) = 1/N^2 := by
    rw [Real.rpow_neg hNp.le,Real.rpow_two,one_div]
  have he1 : N^(-(1:ℝ)) = 1/N := by
    rw [Real.rpow_neg hNp.le,Real.rpow_one,one_div]
  have hsmall : 2*(1/N^2) < 1/N := by
    have hs : 0 < N^2 := sq_pos_of_pos hNp
    have hprod : 0 ≤ (N-4)*(N+2) := by
      apply mul_nonneg <;> linarith only [hN,hNp]
    have hquad : 2*N < N^2 := by nlinarith only [hprod]
    have H : (2:ℝ)/N^2 < 1/N :=
      (div_lt_div_iff₀ hs hNp).mpr (by nlinarith only [hquad])
    simpa only [mul_one_div] using H
  have H := mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 2)
  rw [he2] at H
  rw [he1] at hNU
  exact (H.trans_lt hsmall).trans_le hNU

end OriginalQEq7RegularFamilyPhysicalTailDraft

theorem eventually_eq7_inner_regular_family_from_physical_draft
    (Bclock C eps : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hC : 2 ≤ C) (heps : 0 < eps) :
    ∃ ell : ℕ, 2 < ell ∧ (14+3*delta)/((ell:ℝ)-1) ≤ eps ∧
      ∃ qLow qPost qBroad : ℝ,
        1 ≤ qLow ∧ 1 ≤ qPost ∧ 1 ≤ qBroad ∧
        ∀ᶠ n : ℕ in atTop,
          ∀ (Q : ActualThetaZeroOverlapMinimum
              (n+1) m delta cl cu Az C0 Ct D Bclock)
            (P : Q.Potential) (h : ℝ),
            Q.xs = comparisonConditionalScale
              Q.data.N delta Q.data.E Q.lam →
            Q.data.N^(-(10:ℝ)) ≤ Q.lam →
            h ≤ 1 → h ≤ C*Q.xs →
            ∀ F : Finset (ordConnectedSection P.negativeSet),
              Q.lam*(∑ p : ActualThetaZeroOverlapMinimum.Eq7InnerCoverPiece
                (P.capFamily F) h,
                ActualThetaZeroOverlapMinimum.eq7InnerThermalPiece
                  (P.capFamily F) h p) ≤
              OriginalQEq7RegularFamilyRateDraft.familyConstant
                delta cl Az D C qLow qPost qBroad*
                (Real.log Q.data.N)^6*Q.data.N^(2*delta+eps)*Q.data.E := by
  obtain ⟨ell,hell,horder⟩ :=
    exists_comparison_reverse_moment_order (T:=14+3*delta) heps
  obtain ⟨qLow,hqLow,Hlow⟩ :=
    eventually_eq7_inner_low_piece_physical_draft ell hell Bclock
      hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨qPost,hqPost,Hpost⟩ :=
    eventually_eq7_inner_post_piece_physical_draft ell hell Bclock
      hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨qBroad,hqBroad,Hbroad⟩ :=
    eventually_eq7_inner_broad_slice_physical_draft ell hell Bclock
      hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hnum := eventually_eq7_low_post_original_q_numeric_gates_draft
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az)
    (Ct:=Ct) (D:=D) (Bclock:=Bclock) C0 C qLow qPost eps heps
  have Hcap := eventually_original_q_constraint_length_lower_draft
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az)
    (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm.le hC0
  have Hsmall := ActualThetaZeroOverlapMinimum.eventually_small_mass_le_xs
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    (Bclock:=Bclock) hm hC0
  have Hdepth := (tendsto_add_atTop_nat 1).eventually
    (eventually_comparisonLowerScale_depth hC0 hm)
  have HN : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have HYb := HN.eventually (eventually_ge_atTop (1+32*C))
  refine ⟨ell,hell,horder,qLow,qPost,qBroad,hqLow,hqPost,hqBroad,?_⟩
  filter_upwards [Hlow,Hpost,Hbroad,Hnum,Hcap,Hsmall,Hdepth,HYb]
      with n hnLow hnPost hnBroad hnNum hnCap hnSmall hnDepth hnYb
  intro Q P h hcarrier hlamFloor hhi hh
  let beta : ℝ := 30+10*delta
  let L := Real.log Q.data.N
  let cut := Q.data.N^(-beta)
  rcases hnNum Q with
    ⟨hN,hC0N,_hCN,_hYN,hlog,hlogPow,hN3,hKcutLow,hKcutPost⟩
  have hYb : 1+32*C ≤ Q.data.N := by
    simpa only [ActualHighWallData.N] using hnYb
  have hN4 : 4 ≤ Q.data.N := by linarith only [hYb,hC]
  have hdepth : 1/Q.data.N ≤ Q.data.d := by
    have HD := hnDepth Q.data.E Q.data.d Q.data.hE Q.data.hd Q.hlower
    have HS : comparisonLowerScale Q.data.N Q.data.E Q.data.d ≤
        Q.data.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ Q.data.hd).mpr
        (by simpa only [pow_two] using Q.hupper)
    exact HD.trans HS
  have hUA := hnSmall Q
  have hLcap := hnCap Q
  have hU : Q.data.N^(-(1:ℝ)) ≤
      comparisonSmallMass Q.data.N Q.data.E :=
    hLcap.trans (min_le_left _ _)
  have hbeta : 2 ≤ beta := by dsimp only [beta]; linarith only [hdelta]
  have hcutU : 2*cut < comparisonSmallMass Q.data.N Q.data.E := by
    dsimp only [cut]
    exact OriginalQEq7RegularFamilyPhysicalTailDraft.cut_below_mass hN4 hbeta hU
  have hcutPos : 0 < cut := Real.rpow_pos_of_pos Q.data.hN _
  have hLside : 0 ≤ beta*L :=
    mul_nonneg (by linarith only [hbeta]) (by dsimp only [L]; linarith only [hlog])
  have hlogCut : Real.log (1/cut) ≤ beta*L := by
    have H : Real.log (1/cut) = beta*L := by
      dsimp only [cut,L]
      rw [one_div,Real.log_inv,Real.log_rpow Q.data.hN]
      ring
    exact H.le
  have hLowPhysical : ∀ (F : Finset (ordConnectedSection P.negativeSet))
      (j : Eq7InnerLowDyad Q h),
      eq7InnerThermalPiece (P.capFamily F) h (.inr (.inl j)) ≤
        Q.eq7InnerLowExactBudget ell qLow (beta*L) cut j := by
    intro F j
    simpa only [eq7InnerThermalPiece,eq7InnerCoverSupport,eq7InnerLowExactBudget]
      using hnLow Q P F h j (beta*L) cut hLside hcutPos hlogCut
  have hPostPhysical : ∀ (F : Finset (ordConnectedSection P.negativeSet))
      (j : Eq7InnerPostDyad Q h),
      eq7InnerThermalPiece (P.capFamily F) h (.inr (.inr j)) ≤
        Q.eq7InnerPostExactBudget ell qPost (beta*L) cut j := by
    intro F j
    simpa only [eq7InnerThermalPiece,eq7InnerCoverSupport,eq7InnerPostExactBudget]
      using hnPost Q P F h j (beta*L) cut hLside hcutPos hlogCut
  have hBroadPhysical : ∀ (F : Finset (ordConnectedSection P.negativeSet))
      (b : Eq7InnerRelevantBroadSlice (P.capFamily F) h),
      eq7InnerThermalPiece (P.capFamily F) h (.inl b) ≤
        eq7InnerBroadExactBudget (P.capFamily F) ell qBroad (beta*L) cut b := by
    intro F b
    simpa only [eq7InnerThermalPiece,eq7InnerCoverSupport,eq7InnerBroadExactBudget]
      using hnBroad Q P F b.val (beta*L) cut hLside hcutPos hcutU hlogCut
  have H := ActualThetaZeroOverlapMinimum.Potential.eq7_inner_regular_finite_family_rate_draft
    Q P h hhi ell hell qLow qPost qBroad eps C hm.le hdelta.le heps horder
    hcl hAz hC0 hN hC0N hlog hlogPow hdepth hcarrier hUA hlamFloor
    hC hh hYb hN3 hLcap hqLow hqPost hqBroad hKcutLow hKcutPost
    (by simpa only [beta,L,cut] using hLowPhysical)
    (by simpa only [beta,L,cut] using hPostPhysical)
    (by simpa only [beta,L,cut] using hBroadPhysical)
  exact H

end OAI.SKFluctuations.LaplaceWindowFormalization
