module

public import SKProof.Port.ComparisonActualOriginalQPairedFarRawProduct
public import SKProof.Port.ComparisonActualOriginalQNearPairedGammaRows

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_rest_paired_resampling_working_scale_original_q
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,1 ≤ C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf  →  M.xs ≤ 1  →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs  →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)  →  (∀u∈uniformMasses L,u∈us)  →  ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs  →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        let r:=fun v=>2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v
        ∀(x : ℝ), M.xs ≤ x → x ≤ W →
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (v : ℝ),
          0 < v  →  W ≤ Rmacro/2  →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e)  →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e))  →
          (∀e,G.j e≠j' e  →
            let rh:=M.sweepRadius (partitionPoint 0 as (T.splitIndex (G.j e) (j' e)))
            4*W ≤ rh ∧ M.z ≤ min (rh/8) (Rmacro/4) ∧
            M.sweepRadius (G.sourceLowMass e) ≤ min (rh/8) (Rmacro/4) ∧
            v ≤ partitionPoint 0 as (T.splitIndex (G.j e) (j' e)))  →
        ∀(b s e : T.Slot),s≠e  →
          T.splitIndex b s=T.splitIndex b e  →  T.splitIndex b s < T.splitIndex s e  →
          (let rh:=M.sweepRadius (partitionPoint 0 as (T.splitIndex s e));
            4*W ≤ rh ∧ M.z ≤ min (rh/8) (Rmacro/4) ∧
            M.sweepRadius (partitionPoint 0 as (T.splitIndex b s)) ≤ min (rh/8) (Rmacro/4) ∧
            v ≤ partitionPoint 0 as (T.splitIndex s e))  →
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>(nativeRestEndpointDifference n T b s e σ*
            ((G.canonicalOriginalQSource M f).restProduct σ-
              ((G.retarget j' hne).canonicalOriginalQSource M f).restProduct σ))^2) 0 ≤
          ((a:ℝ)*(r v)*((1+Temp)*(r v)/x)*
            (C^a*sourceMonomialScale x W initial))^2 := by
  obtain ⟨C,hC,Hmom⟩:=eventually_actual_inherited_canonical_rest_paired_product_from_resampling_original_q
    (D:=D) a ha Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hsave:=eventually_actual_minimum_inherited_rest_all_high_resampling_original_q (D:=D) a
    Bclock Temp Cf Ccal Rmacro F hCf hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hCcal hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [Hmom,Hsave,eventually_gt_atTop (0:ℕ)] with n hmom hsave hn
  intro M hs0 hsxs hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hmom M hs0 hsxs hsource hxs L us hus hret hmesh,
    hsave M hs0 hsxs hsource hxs hcompare L us hus hret hmesh] with k hk hksave
  dsimp only at hk hksave ⊢
  intro x hxsx hxW T G f initial v hv hWmacro hmass j' hne hlow hgeometry b s e hse hblow hbgap hgeom
  let as:=finiteCutMasses us k
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
  let r:=2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v
  have hxsW : M.xs ≤ W:=le_max_left _ _
  have hW : 0 < W:=M.hxs.trans_le hxsW
  have hxspos:=M.hxs
  have hr : 0 < r:=mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos
    (by exact_mod_cast hn : (0:ℝ) < n) _))
    (savedExteriorScale_pos (by positivity) hW hv)
  have Hsaved (lo hi : ℕ) (hhi : hi ≤ as.length)
      (HG : 4*W ≤ M.sweepRadius (partitionPoint 0 as hi) ∧
        M.z ≤ min (M.sweepRadius (partitionPoint 0 as hi)/8) (Rmacro/4) ∧
        M.sweepRadius (partitionPoint 0 as lo) ≤ min (M.sweepRadius (partitionPoint 0 as hi)/8) (Rmacro/4) ∧
        v ≤ partitionPoint 0 as hi) :
      originalBoundaryResamplingMoment n (a+1) as
        (fun j=>restFiniteRealVariance n (Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ))
          (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ)))) lo hi ≤ r^(2*(a+1)) := by
    obtain ⟨hRh,hz,hRl,hvhi⟩:=HG
    have H:=hksave lo hi hhi hWmacro hRh hz hRl
    apply H.trans
    apply pow_le_pow_left₀ (by
      apply mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      unfold savedExteriorScale
      positivity)
    exact mul_le_mul_of_nonneg_left
      (savedExteriorScale_antitone_mass (by positivity) hW hv hvhi) (by positivity)
  apply hk T G f initial x W r hxsx hxW hr hmass j' hne hlow
  · intro j hj
    obtain ⟨hRh,_,hRl,_⟩:=hgeometry j hj
    have hrh : 0 < M.sweepRadius (partitionPoint 0 as (T.splitIndex (G.j j) (j' j))):=
      lt_of_lt_of_le (by positivity : 0 < 4*W) hRh
    have hlower:=hRl.trans (min_le_left _ _)
    by_contra hnot
    have H:=M.R_monotone (partitionPoint_mono as
        (finiteCutMasses_ordered us hus k) (show T.splitIndex (G.j j) (j' j) ≤
          T.splitIndex (G.i j) (G.j j) by omega))
    change M.sweepRadius (partitionPoint 0 as (T.splitIndex (G.j j) (j' j))) ≤ M.sweepRadius (G.sourceLowMass j) at H
    linarith
  · intro j hj
    exact Hsaved _ _ (T.splitIndex_le_clockLength _ _) (hgeometry j hj)
  · exact hse
  · exact hblow
  · exact hbgap
  · exact Hsaved _ _ (T.splitIndex_le_clockLength _ _) hgeom

end OAI.SKFluctuations.Cavity
