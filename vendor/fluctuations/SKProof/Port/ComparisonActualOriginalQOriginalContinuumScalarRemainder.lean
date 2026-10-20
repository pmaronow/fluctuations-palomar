module

public import ComparisonScalarOriginalNonstrictBufferRemainder
public import SKProof.Port.OriginalQHighOnlyBridge
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import ComparisonSignedCavityContinuumMixedClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false

theorem eventually_actual_cavity_context_original_continuum_scalar_remainder_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (A : ℝ) (hA : 0≤A)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M Temp)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0)) :
    ∃R : ℝ,0<R ∧ ∀ᶠn in atTop,
      ∀(before after : List PositiveMass) (a : PositiveMass),
        MassOrdered 0 (before++a::after) →
      ∀j V : ℕ,j<before.length+1 → before.length+1≤V →
        V≤(before++a::after).length →
        a.val<partitionPoint 0 (before++a::after) V →
        partitionPoint 0 (before++a::after) V≤A*(W n) →
      ∀(tree : ClockTree (Spin (dim n)×Bool) (before++a::after))
        (start : ℝ) (_hoa : MassOrdered start (before++a::after)) (s : tree.Slot),
      let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf (before++a::after)
      let chi:=((tree.markedAttach start).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree (before.length+1) K (p.embed s) p.mark)).sum
      |nativeOriginalScalarPairMean (before++a::after) K j-chi^2*K j|≤
        nativeScalarLowRemainderConstant A R R*(W n)^3 := by
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_mass_mean_upper_original_q
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ck:=G.Cf+Temp*Cs
  have hCk : 0≤Ck:=by dsimp only [Ck];positivity [G.hCf_original_q,G.hT.le]
  let R:=Ck*(1+A)+1
  have hR : 0<R:=by dsimp only [R];positivity
  have Hsmall : ∀ᶠn in atTop,R*W n≤1:=
    (hWlim.const_mul R).eventually (eventually_le_nhds (by simp : R*(0:ℝ)<1))
  refine ⟨R,hR,?_⟩
  filter_upwards [hdim.eventually HS,G.eventually_geometric_gates_original_q,(G.source_eventually_original_q hcl),G.total_root_bare_original_q,Hsmall]
    with n hn hnGates hnSource hnRoot hnSmall
  intro before after a ho j V hj hUV hV hbuffer hsize tree start hoa s
  let as:=before++a::after
  let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
  have hW : 0≤W n:=((M n).hxs.trans_le (hxs n)).le
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone
    (dim n) (M n).sweepBf (M n).sweepHf (M n).sweep_bf_monotone (M n).sweep_hf_monotone as ho
  have hzero : K 0=0:=by
    simp [K,nativeContinuumMixedClock,partitionPoint,
      (M n).inherited_zero_root_field hnRoot.2,orderedPathS,orderedPathPair_zero]
  have Hclock l : K l≤Ck*((M n).xs+partitionPoint 0 as l):=by
    have hu:=partitionPoint_mem as ho l
    have HS' : orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as l)≤
        Cs*((M n).xs+partitionPoint 0 as l):=by
      by_cases hp : 0<partitionPoint 0 as l
      · exact hn (M n) hnGates.2 hnGates.1 _ ⟨hp,hu.2⟩
      · have hz : partitionPoint 0 as l=0:=le_antisymm (le_of_not_gt hp) hu.1
        rw [hz,orderedPathS,orderedPathPair_zero]
        simpa only [add_zero] using mul_nonneg hCs.le (M n).hxs.le
    have HC:=hnSource _ hu
    have Hprod:=mul_le_mul HC.1 HS'
      ((M n).mass_mean_unit_bounds hu).1 G.hT.le
    dsimp only [K,nativeContinuumMixedClock,Ck]
    nlinarith only [HC.2,Hprod]
  have Hbound l (hl : l≤V) : K l≤R*W n:=by
    have Hmass:=partitionPoint_mono as ho hl
    have Hsize : (M n).xs+partitionPoint 0 as l≤(1+A)*W n:=by
      nlinarith only [hxs n,hsize,Hmass]
    have H:=(Hclock l).trans (mul_le_mul_of_nonneg_left Hsize hCk)
    dsimp only [R]
    nlinarith only [H,hW]
  exact native_gamma_row_scalar_low_remainder_of_nonstrict_buffer (dim n)
    before after a ho K hKm hzero hW hA hR.le hR.le j V hj hUV hV hbuffer hsize
    (Hbound j (hj.le.trans hUV)) (Hbound (before.length+1) hUV)
    ((Hbound j (hj.le.trans hUV)).trans hnSmall) tree start hoa s

end OAI.SKFluctuations.LaplaceWindowFormalization
