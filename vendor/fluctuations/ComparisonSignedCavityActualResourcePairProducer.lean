module

public import ComparisonSignedCavityActualResourcePairBudgets

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualResourcePairBudgetOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree : ℕ) (A saving Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val≤1)→(w n).star∈us→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤(M n).xs→
    ∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
      let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
      ∀(U i k : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [.initial] k T P→1+k≤degree→i≤as.length→
        ∀x : ℝ,(M n).xs≤x→x≤W n→partitionPoint 0 as i≤Cmass*x→
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as b h 0 0)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n (M n).bf (M n).hf as) 0
          A x (W n) (((n+1:ℕ):ℝ)^(-saving))

theorem actual_resource_pair_budget_of_actual_pair_producers
    (degree : ℕ) (hd : 0 < degree)
    {m delta cl cu Az C0 Ct D Bclock Temp saving : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hTemp : 0≤Temp) (Cmass : ℝ) (hCm : 0≤Cmass)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0)
    (w : ℕ→ActualSlowWindowChoice)
    (Hstar : ActualOriginalRestStarFiniteDegreeOnEveryFinalNet degree saving M W w) :
    ∃A : ℝ,1≤A ∧ ActualResourcePairBudgetOnEveryFinalNet degree A saving Cmass M W w := by
  obtain ⟨Cin,hCin,Hinitial⟩:=eventually_actual_minimum_initial_centered_pair_even_moment degree hd
    Bclock Temp Cmass hTemp hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let A:=max 1 Cin
  have hA1 : 1≤A:=le_max_left _ _
  have hCA : Cin≤A:=le_max_right _ _
  refine ⟨A,hA1,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [Hinitial,Hstar,HW,eventually_gt_atTop (0:ℕ)] with n hn hsn hnW hn0
  intro L us hus hstar hret hmesh
  have hMxs : (M n).xs≤1:=(hxs n).trans hnW
  filter_upwards [hn (M n) (hb n) (hh n) hMxs L us hus hret hmesh,hsn us hus hstar] with j hj hsj
  dsimp only at hj hsj ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
  let ho:=finiteCutMasses_ordered us hus j
  let center:=nativePhysicalResourceCenter n (M n).bf (M n).hf as
  let ε:=((n+1:ℕ):ℝ)^(-saving)
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have heps : 0 < ε:=by dsimp only [ε];positivity
  have hNode : partitionPoint 0 as star=(w n).star.val :=
    nativeRetainedCut_partitionPoint as ho (w n).star (finiteCutMasses_nodes us j hstar)
  have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hCenterStar : center star=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val := by
    dsimp only [center]
    rw [native_physical_resource_center_at_positive_cut n (M n).bf (M n).hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) as ho star
      (by rw [hNode];exact (w n).star.property),hNode]
  intro U i k T P hP hdegree hi x hxsx hxW hmass
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  let q:=finitePhysicalCavitySquareVariance n U as b h 0 0
  let R:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)
  apply hP.pairMomentBudget_of_initial_star_bounds degree hdegree (fullWeight n) (fullFeature n) 0 q
    R center 0 A x (W n) ε
  · intro l hl hlD
    let V:=ClockTree.pairClock (S:=Spin n×Bool) as i
    let F:=fun σ : V.Assignment=>R (ClockTree.pairSpin as i σ).1 (ClockTree.pairSpin as i σ).2-center i
    have HH:=hj U i hi x hxsx hmass
    have HH' : V.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>|F σ|^(2*degree)) 0≤
        (A*x)^(2*degree) := HH.trans (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right hCA hx.le) _)
    have Hlow:=V.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 q 0 F
      (p:=(2*l:ℕ)) (r:=(2*degree:ℕ)) (by exact_mod_cast (show 0<2*l by omega))
      (by exact_mod_cast (show 2*l≤2*degree by omega)) (by positivity : 0≤A*x)
      (by simpa only [Real.rpow_natCast] using HH')
    simpa only [Real.rpow_natCast,V,F] using Hlow
  · intro l hl hlD
    change (ClockTree.pairClock as star).disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as star σ).1)
        (joinSpin (ClockTree.pairSpin as star σ).2)-center star|^(2*l)) 0≤(A*(ε*W n))^(2*l)
    rw [hCenterStar,native_full_decoupled_centered_pair_eq_rest n l hn0 ho b h U star
      (retainedMassPrefixIndex_le_length (w n).star.val as)]
    exact (hsj l hl hlD).trans (pow_le_pow_left₀ (by positivity)
      (le_mul_of_one_le_left (by positivity : 0≤ε*W n) hA1) _)

theorem exists_actual_bare_resource_pair_budget_sequence
    {m delta cl cu Az C0 Ct D Bclock Temp Lwin Ccal : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hTemp : 0 < Temp) (hL : 0 < Lwin) (hCcal : 1≤Ccal)
    (Cmass : ℝ) (hCm : 0≤Cmass)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ)
    (hcanonical : ∀n,W n=max (M n).xs
      (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)))
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2≤Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) Temp Lwin Cs (w n)) ∧
      ∀degree : ℕ,0 < degree→∃A : ℝ,1≤A ∧
        ActualResourcePairBudgetOnEveryFinalNet degree A saving Cmass M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,H,Hfinite⟩:=exists_actual_bare_original_rest_star_on_every_final_net
    hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hL hCcal M W hcanonical hWlim hcompare hb hh
  refine ⟨hs,Cs,hCs,w,hw,?_⟩
  intro degree hd
  exact actual_resource_pair_budget_of_actual_pair_producers degree hd hm hdelta hroom hcl hcu hAz hC0 hCt
    hTemp.le Cmass hCm M W (fun n=>by rw [hcanonical];exact le_max_left _ _) hWlim hb hh w (Hfinite degree)

end OAI.SKFluctuations.LaplaceWindowFormalization
