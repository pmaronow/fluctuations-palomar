module

public import ComparisonActualGeneralInitialPairSecondTransport
public import ComparisonActualHighWallLowProfileMoments
public import ComparisonActualHighWallAllDegreeContinuumMoments
public import ComparisonActualHighWallSourceClockBudget

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

def originalHighWallInitialPairErrorScale
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i : ℕ) : ℝ :=
  originalInitialPairComparisonConstant (2*max Bclock 0) (max Bclock 0)*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))

theorem original_high_wall_initial_pair_error_scale_nonneg
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i : ℕ) : 0 ≤ originalHighWallInitialPairErrorScale M as i := by
  unfold originalHighWallInitialPairErrorScale
  exact mul_nonneg (original_initial_pair_comparison_constant_pos _ _).le
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))

theorem actual_high_wall_bare_initial_pair_second_moment
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (U : ℕ)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (i : ℕ) (hi : i ≤ as.length) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    (pairClock as i).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
      (fun σ=>|deletedOverlap n (joinSpin (pairSpin as i σ).1)
        (joinSpin (pairSpin as i σ).2)-S i|^2) 0 ≤
      (originalHighWallInitialPairErrorScale M as i)^2 := by
  apply actual_original_initial_pair_second_transport n U M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) ho hl ht
  · intro j _
    have H:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho j)
    exact (show (M.bf (partitionPoint 0 as j):ℝ) ≤ M.data.T by
      linarith [(M.hf (partitionPoint 0 as j)).coe_nonneg]).trans
      (M.hT.trans (le_max_left _ _))
  · have hu:=partitionPoint_mem as ho as.length
    have H:=M.data.total_clock_le M.alpha _ hu
    have HS:=physicalOrderedPathS_mem_unit n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hu
    have Hmul:=mul_le_mul_of_nonneg_left HS.2 (M.bf (partitionPoint 0 as as.length)).coe_nonneg
    have HT:=M.hT.trans (le_max_left Bclock 0)
    nlinarith only [H,Hmul,HT]
  · exact hi

theorem eventually_actual_high_wall_initial_pair_moment_interpolate
    (p : ℕ) (hp : 0 < p) (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cr : ℝ,0 < Cr ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        ∀(U : ℕ) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        ∀i,i ≤ as.length → partitionPoint 0 as i ≤ Ccut*M.data.d →
          let error:=originalHighWallInitialPairErrorScale M as i
          let eta:=originalInitialLowMomentModulus error (Cr*M.data.d) (2*p)
          (pairClock as i).disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|deletedOverlap n (joinSpin (pairSpin as i σ).1)
              (joinSpin (pairSpin as i σ).2)-S i|^(2*p)) 0 ≤ (Cr*M.data.d*eta)^(2*p) := by
  obtain ⟨Cr,hCr,Hhigh⟩:=eventually_actual_high_wall_centered_low_pair_moment
    (D:=D) (2*p-1) (by omega) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cr,hCr,?_⟩
  filter_upwards [Hhigh] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U l t hl ht i hi hmass
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let law:=cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K
  let F:=fun σ : (pairClock (S:=Spin n×Bool) as i).Assignment=>
    deletedOverlap n (joinSpin (pairSpin as i σ).1) (joinSpin (pairSpin as i σ).2)-S i
  let error:=originalHighWallInitialPairErrorScale M as i
  have he : 0 ≤ error:=original_high_wall_initial_pair_error_scale_nonneg M as i
  have hR : 0 < Cr*M.data.d:=mul_pos hCr M.data.hd
  have Htwo : (pairClock as i).disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>(F σ)^2) 0 ≤ error^2:=by
    simpa only [sq_abs,F,law,error,K,S,b,h,as] using
      actual_high_wall_bare_initial_pair_second_moment M as (finiteCutMasses_ordered us hus jGrid)
        U hl ht i hi
  have Hh : (pairClock as i).disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|F σ|^(4*p-2)) 0 ≤ (Cr*M.data.d)^(4*p-2):=by
    have H:=hj U l t hl ht i hi hmass
    simpa only [show 2*(2*p-1)=4*p-2 by omega,F,law,K,S,b,h,as] using H
  have H:=disorderExpect_initial_low_even_moment_interpolate (fullWeight_pos n) (fullFeature n)
    (pairClock as i) (finiteCutMasses_ordered us hus jGrid) 0 law 0 F p hp he hR.le Htwo Hh
  exact H.trans_eq (original_initial_low_interpolation_scale_pow he hR (2*p) (by omega)).symm

end OAI.SKFluctuations.Cavity
