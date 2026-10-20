module

public import SKProof.Port.ComparisonActualOriginalQRawResourcePairBudget
public import ComparisonSignedCavityActualInheritedSquareResourceAlong
public import SKProof.Port.ComparisonActualOriginalQSquareConsumerActualInheritedSquareStarAlong

@[expose] public section
set_option linter.unusedVariables false
noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum ActualThetaZeroOverlapMinimum

def ActualSquareResourcePairBudgetOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree : ℕ) (A saving Cmass : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val≤1)→(w n).star∈us→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤(M n).xs→
    ∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      let b:=fun k=>((M n).sweepBf (partitionPoint 0 as k):ℝ)
      let h:=fun k=>((M n).sweepHf (partitionPoint 0 as k):ℝ)
      ∀(U i k : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [.initial] k T P→1+k≤ degree→i≤ as.length→
        ∀x : ℝ,(M n).xs≤ x→x≤ W n→partitionPoint 0 as i≤ Cmass*x→
        ∀a t : ℝ,a∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→P.PairMomentBudget (fullWeight (dim n)) (fullFeature (dim n)) 0
          (finitePhysicalCavitySquareVariance (dim n) U as b h a t)
          (fun σ τ=>deletedOverlap (dim n) (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter (dim n) (M n).sweepBf (M n).sweepHf as) 0
          A x (W n) (((dim n+1:ℕ):ℝ)^(-saving))

theorem actual_inherited_square_resource_pair_budget_of_actual_pair_producers_along_original_q
    (degree : ℕ) (hd : 0 < degree)
    {m delta cl cu Az C0 Ct D Bclock Temp Cf saving : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤ Az) (hC0 : 0 < C0) (hCt : 0≤ Ct)
    (hTemp : 0≤ Temp) (hCf : 0≤ Cf) (Cmass : ℝ) (hCm : 0≤ Cmass)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hsmall : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (Hstar : ActualOriginalSquareStarMomentOnEveryFinalNetAlong_original_q (degree-1) saving M W w) :
    ∃A : ℝ,1≤ A ∧ ActualSquareResourcePairBudgetOnEveryFinalNetAlong_original_q degree A saving Cmass M W w := by
  obtain ⟨Cin,hCin,Hinitial⟩:=eventually_actual_minimum_inherited_raw_resource_initial_pair_even_moment_original_q degree hd
    Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let A:=max 1 Cin
  have hA1 : 1≤ A:=le_max_left _ _
  have hCA : Cin≤ A:=le_max_right _ _
  refine ⟨A,hA1,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually Hinitial,Hstar,HW,hdim.eventually (eventually_gt_atTop (0:ℕ)),hsource,hsmall] with n hn hsn hnW hn0 hnsource hnsmall
  intro L us hus hstar hret hmesh
  have hMxs : (M n).xs≤1:=(hxs n).trans hnW
  filter_upwards [hn (M n) hnsmall.1 hnsmall.2 hnsource hMxs L us hus hret hmesh,hsn us hus hstar] with j hj hsj
  dsimp only at hj hsj ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun k=>((M n).sweepBf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).sweepHf (partitionPoint 0 as k):ℝ)
  let ho:=finiteCutMasses_ordered us hus j
  let center:=nativePhysicalResourceCenter (dim n) (M n).sweepBf (M n).sweepHf as
  let ε:=((dim n+1:ℕ):ℝ)^(-saving)
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have heps : 0 < ε:=by dsimp only [ε];positivity
  have hNode : partitionPoint 0 as star=(w n).star.val :=
    nativeRetainedCut_partitionPoint as ho (w n).star (finiteCutMasses_nodes us j hstar)
  have hCenterStar : center star=orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (w n).star.val := by
    dsimp only [center]
    rw [native_physical_resource_center_at_positive_cut (dim n) (M n).sweepBf (M n).sweepHf
      ((M n).sweep_bf_monotone) ((M n).sweep_hf_monotone) as ho star
      (by rw [hNode];exact (w n).star.property),hNode]
  intro U i k T P hP hdegree hi x hxsx hxW hmass a t ha ht
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  let q:=finitePhysicalCavitySquareVariance (dim n) U as b h a t
  let R:=fun σ τ : Spin (dim n)×Bool=>deletedOverlap (dim n) (joinSpin σ) (joinSpin τ)
  apply hP.pairMomentBudget_of_initial_star_bounds degree hdegree (fullWeight (dim n)) (fullFeature (dim n)) 0 q
    R center 0 A x (W n) ε
  · intro l hl hlD
    let V:=ClockTree.pairClock (S:=Spin (dim n)×Bool) as i
    let F:=fun σ : V.Assignment=>R (ClockTree.pairSpin as i σ).1 (ClockTree.pairSpin as i σ).2-center i
    have HH:=hj U i a t ha ht hi x hxsx hmass
    have HH' : V.disorderExpect (fullWeight (dim n)) (fullFeature (dim n)) 0 q (fun σ=>|F σ|^(2*degree)) 0≤
        (A*x)^(2*degree) := HH.trans (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right hCA hx.le) _)
    have Hlow:=V.disorderExpect_rpow_moment_le (fullWeight_pos (dim n)) (fullFeature (dim n)) ho 0 q 0 F
      (p:=(2*l:ℕ)) (r:=(2*degree:ℕ)) (by exact_mod_cast (show 0<2*l by omega))
      (by exact_mod_cast (show 2*l≤2*degree by omega)) (by positivity : 0≤ A*x)
      (by simpa only [Real.rpow_natCast] using HH')
    simpa only [Real.rpow_natCast,V,F] using Hlow
  · intro l hl hlD
    let V:=ClockTree.pairClock (S:=Spin (dim n)×Bool) as star
    let F:=fun σ : V.Assignment=>R (ClockTree.pairSpin as star σ).1 (ClockTree.pairSpin as star σ).2-center star
    have horder : degree-1+1=degree := by omega
    have Hstar:=hsj U a t ha ht
    simp only [horder] at Hstar
    have HH' : V.disorderExpect (fullWeight (dim n)) (fullFeature (dim n)) 0 q
        (fun σ=>|F σ|^(2*degree)) 0≤(A*(ε*W n))^(2*degree) := by
      change nativeOriginalSquareCenteredMoment (dim n) degree U as b h star (center star) a t≤_
      rw [hCenterStar]
      exact Hstar.trans (pow_le_pow_left₀ (by positivity)
        (le_mul_of_one_le_left (by positivity : 0≤ε*W n) hA1) _)
    have Hlow:=V.disorderExpect_rpow_moment_le (fullWeight_pos (dim n)) (fullFeature (dim n)) ho 0 q 0 F
      (p:=(2*l:ℕ)) (r:=(2*degree:ℕ)) (by exact_mod_cast (show 0<2*l by omega))
      (by exact_mod_cast (show 2*l≤2*degree by omega)) (by positivity : 0≤ A*(ε*W n))
      (by simpa only [Real.rpow_natCast] using HH')
    simpa only [Real.rpow_natCast,V,F] using Hlow

end OAI.SKFluctuations.LaplaceWindowFormalization
