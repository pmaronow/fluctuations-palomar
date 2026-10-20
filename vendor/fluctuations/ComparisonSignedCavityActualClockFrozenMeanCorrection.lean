module

public import ComparisonSignedCavityActualOriginalClockResponse
public import ComparisonSignedCavityActualOriginalClockMeanSaving
public import ComparisonSignedCavityActualFrozenMeanResourceCorrection
public import ComparisonSignedCavityOriginalPhysicalClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Filter Set LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

theorem native_original_clock_constant_pairing_eq_mean
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (U : ℕ) (K b h C : ℕ→ℝ) (a : T.Slot) :
    nativeOriginalLongitudinalPairing n 0
      (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 U K b C T (fun _=>1) a=
      nativeOriginalLongitudinalMean T U K b h C a := by
  have Hq : finitePhysicalCavitySquareVariance n U as b h 1 1=
      cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K := by
    exact native_full_endpoint_clock_mixed_independent n _ U 1 b h _ K
  simp only [nativeOriginalLongitudinalPairing,nativeOriginalLongitudinalMean,Hq,one_mul]

theorem nativeOriginalClockResourceResponse_freeze_abs_le
    {n : ℕ} {as : List PositiveMass} {i star U k : ℕ} {seed : List NativeResourceMark}
    {T : ClockTree (Spin n×Bool) as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (ho : MassOrdered 0 as)
    (K b h C : ℕ→ℝ) (A x W ε B : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 A x W ε)
    (hmean : |nativeOriginalLongitudinalMean T U K b h C P.live.test.target|≤B) :
    let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
    |nativeOriginalClockResourceResponse P.freeze U k K b C 0 q 0 0 q 0 W|≤
      (|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k)*B := by
  dsimp only
  have H:=hP.normalized_mean_abs_le (fullWeight_pos n) (fullFeature n) ho 0 _
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 A x W ε
    hA hx hW hε hi hstar hm
  have hscale : 0≤nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro b hb
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
    exact (a.savedScale_pos hx hW hε).le
  rw [nativeOriginalClockResourceResponse_freeze P ho,
    native_original_clock_constant_pairing_eq_mean,neg_mul,abs_mul,abs_neg]
  exact mul_le_mul H hmean (abs_nonneg _) (by positivity)

theorem eventually_actual_clock_frozen_resource_correction
    (r : ℕ) (Bclock Temp : ℝ) (hTemp : 0≤Temp)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hcl : 0 < cl) (hAz : 0≤Az) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp)→(∀u,M.h u=0)→
      ∀us : List PositiveMass,(∀u∈us,u.val≤1)→∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
        let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
        ∀(K : ℕ→ℝ) (i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P→T.leaves≤r→
        ∀A x W ε : ℝ,0<A→0<x→0<W→0<ε→i ≤ star→star<as.length→
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as b h 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W ε→
        |nativeOriginalClockResourceResponse P.freeze U k K b
          (nativePhysicalResourceCenter n M.bf M.hf as)
          0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
          0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 W|≤
          (|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k)*
            (((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2) := by
  filter_upwards [eventually_actual_minimum_original_clock_longitudinal_mean_saving r Bclock Temp
    hTemp hm hcl hAz hC0] with n hn
  intro M hb hh us hus
  filter_upwards [hn M hb hh us hus] with j hj
  dsimp only at hj ⊢
  intro K i star U k seed T P hP hT A x W ε hA hx hW hε hi hstar hbudget
  exact nativeOriginalClockResourceResponse_freeze_abs_le hP (finiteCutMasses_ordered us hus j)
    K _ _ _ A x W ε _ hA hx hW hε hi hstar hbudget (hj K T U P.live.test.target hT)

end OAI.SKFluctuations.Cavity
