module

public import ComparisonSignedCavityActualGCentering
public import ComparisonSignedCavityActualWeightedGTerminal

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

theorem NativeActualResourceGenerated.normalized_mean_abs_le
    {as : List PositiveMass} {i star U : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (R : S→S→ℝ) (C : ℕ→ℝ) (x₀ : ι→ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm : P.PairMomentBudget w φ v q R C x₀ A x W ε) :
    |(W⁻¹)^k*T.disorderExpect w φ v q (P.value w φ v q R C x₀) x₀|≤
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k := by
  have HG : T.disorderExpect w φ v q (fun _=>(1:ℝ)^2) x₀≤(1:ℝ)^2 := by
    simp [T.disorderExpect_one hw φ ho]
  have H:=hP.normalized_terminal_pairing_sq_le hw φ ho v q R C x₀ A x W ε
    hA hx hW hε hi hstar hm (fun _=>1) 1 HG
  simp only [mul_one,T.disorderExpect_const_mul hw φ ho] at H
  have hscale : 0≤nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro b hb
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
    exact (a.savedScale_pos hx hW hε).le
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using H)

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem nativeActualResourceGInsertion_freeze_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U k : ℕ} {seed : List NativeResourceMark}
    {T : ClockTree (Spin n×Bool) as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (ho : MassOrdered 0 as)
    (A x W ε B : ℝ) (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W ε)
    (hmean : |nativeOriginalLongitudinalMean T U
      (finitePhysicalMixedClock (n+1) as (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun j=>(M.hf (partitionPoint 0 as j):ℝ)))
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
      (nativePhysicalResourceCenter n M.bf M.hf as) P.live.test.target|≤B) :
    |nativeActualResourceGInsertion M P.freeze U k 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1) 0 W|≤
      (|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k)*B := by
  have H:=hP.normalized_mean_abs_le (fullWeight_pos n) (fullFeature n) ho 0 _
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W ε hA hx hW hε hi hstar hm
  have hscale : 0≤nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro b hb
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
    exact (a.savedScale_pos hx hW hε).le
  rw [nativeActualResourceGInsertion_freeze_eq_original_mean M P ho U k W]
  rw [neg_mul,abs_mul,abs_neg]
  exact mul_le_mul H hmean (abs_nonneg _) (by positivity)

theorem eventually_actual_frozen_resource_correction
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
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P→T.leaves≤r→
        ∀A x W ε : ℝ,0<A→0<x→0<W→0<ε→i ≤ star→star<as.length→
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as b h 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W ε→
        |nativeActualResourceGInsertion M P.freeze U k 0
          (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 W|≤
          (|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k)*
            (((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2) := by
  filter_upwards [eventually_actual_minimum_original_longitudinal_mean_saving r Bclock Temp
    hTemp hm hcl hAz hC0] with n hn
  intro M hb hh us hus
  filter_upwards [hn M hb hh us hus] with j hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hT A x W ε hA hx hW hε hi hstar hbudget
  exact nativeActualResourceGInsertion_freeze_abs_le M hP (finiteCutMasses_ordered us hus j)
    A x W ε _ hA hx hW hε hi hstar hbudget (hj T U P.live.test.target hT)

end OAI.SKFluctuations.Cavity
