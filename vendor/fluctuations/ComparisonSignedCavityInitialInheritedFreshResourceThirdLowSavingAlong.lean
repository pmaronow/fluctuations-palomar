module

public import ComparisonSignedCavityInitialInheritedCenteredResourceThirdLowSavingAlong
public import ComparisonSignedCavityActualResourceLowTaylorReadout
public import ComparisonSignedCavityActualCenteredResourceLowTaylorReadout
public import ComparisonSignedCavityActualFreshResourceLowTaylorReadout
public import ComparisonSignedCavityInheritedRawResourcePairBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_fresh_resource_third_LOW_saving_along
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Cinitial Couter : ℝ)
    (hTemp : 0≤ Temp) (hCf : 0≤ Cf) (hCm : 0≤ Cmass) (hCinitial : 0≤ Cinitial) (hCouter : 0< Couter)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) (hCs : 0≤ Cs)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (HS : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃Ci : ℝ,0< Ci ∧ ∃err : ℕ→ℝ,(∀n,0≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),(∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→
        ((L+1:ℕ):ℝ)⁻¹≤(M n).xs→(w n).star∈us→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i V U k : ℕ) (seed : List NativeResourceMark) (T : ClockTree (Spin (dim n)×Bool) as)
          (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed k T P→U≤ as.length→T.leaves≤ rBound→seed.length+k≤ degree→
          0< V→i< V→V≤ star→star< U→partitionPoint 0 as V≤ Cinitial*(M n).xs→
          partitionPoint 0 as i≤ Cmass*(M n).xs→partitionPoint 0 as star≤ Cmass*W n→
          partitionPoint 0 as U≤ Couter*W n→
        ∀(l t : ℝ),l∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        |((W n)⁻¹)^k*nativeActualOriginalFreshResourceThirdLowPart (M n) U P l t|≤
          |P.coefficient| * nativeResourceScale (M n).xs (W n) 1 seed*
            (Ci*W n*(M n).xs*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
              err n*W n*(M n).xs^2) := by
  obtain ⟨Ci,hCi,err,herr,Herr,H⟩:=actual_inherited_initial_centered_resource_third_LOW_saving_along
    degree (rBound+1) Bclock Temp Cf Cmass Cinitial Couter hTemp hCf hCm hCinitial hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M W hcanonical hWlim HS hsmall Hclock w hw
  refine ⟨Ci,hCi,err,herr,Herr,?_⟩
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hStarNode
  filter_upwards [hn L us hus hret hmesh hStarNode] with jGrid hj
  dsimp only at hj ⊢
  intro i V U k seed T P hP hU hT hdepth hV hiV hVstar hstar hcutI hmi hms hcut l t hl ht
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hg:g.tree.leaves≤ rBound+1:=by
    have HH:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have Hsplit:g.tree.splitIndex (g.embed P.live.test.target) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,min_eq_left (hstar.le.trans hU)]
  have haz:g.embed P.live.test.target≠g.mark:=by
    intro heq
    have HH:=Hsplit
    rw [heq,g.tree.splitIndex_self] at HH
    dsimp only [star,as] at HH
    omega
  have HO:=hj i V U k seed g.tree (P.retarget 0) hP.retarget hU hg hdepth hV hiV hVstar hstar hcutI hmi hms hcut
    (g.embed P.live.test.target) g.mark l t haz (by rw [Hsplit];exact hVstar) hl ht
  rw [native_actual_original_fresh_resource_third_LOW_eq_centered_retarget (M n) U P ho]
  simpa only [NativeResourceTerm.retarget] using HO

end OAI.SKFluctuations.Cavity
