module

public import ComparisonSignedCavityGroupedBoundaryRates
public import ComparisonSignedCavityGroupedRawTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

structure OriginalBoundaryPrimitiveInput (n k dc dq : ℕ) (as : List PositiveMass)
    (q : ℕ→FeatureIndex n→ℝ) (low high : ℕ) (B A Cq H₀ c₀ r W v : ℝ) where
  c : ℝ
  D₀ : ℝ
  xs : ℝ
  H : ℝ
  actualLowMass : c=physicalCutMass 0
    (clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1)))) low
  Dpos : 0<D₀
  xspos : 0<xs
  Hnonneg : 0 ≤ H
  ordered : OrderedSteps c (originalBoundaryTailSteps n as q low)
  cs : List (ℝ×ℕ)
  anchor : Fin cs.length→ℝ
  duration : Fin cs.length→ℝ
  last : lastLayerCut cs (high-low)=(originalBoundaryTailSteps n as q low).length+1
  ends : ∀ j : Fin cs.length,
    cutPredecessor cs (high-low) j ≤ (cs.get j).2 ∧
      (cs.get j).2 ≤ (originalBoundaryTailSteps n as q low).length+1
  clocks : ∀ j,0<anchor j ∧ D₀ ≤ duration j ∧ duration j ≤ B ∧
    PhysicalProjectionClock n (originalBoundaryTailSteps n as q low) 0
      (cutPredecessor cs (high-low) j) (cs.get j).2 (anchor j) (duration j)
  scales : ∀ i j,i ≤ j.succ → xs+physicalCutMass c (originalBoundaryTailSteps n as q low)
    (overlapComponentEnd cs (high-low) i) ≤ H*(anchor j)^2
  count : ((physicalOverlapResidualPairs cs).card:ℝ)^2 ≤ A*(Real.log (n:ℝ))^dc
  fullRaw : (physicalRawRatio n (k+1)
    (clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1)))) 0 xs
    (Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))) id measurable_id)^2 ≤
      Cq*(Real.log (n:ℝ))^dq
  highAnchor : H ≤ H₀/v
  innovation : c₀*W^3/Real.log (n:ℝ) ≤ D₀

theorem eventually_original_boundary_resampling_from_primitives
    (k dc dq : ℕ) (B A Cq H₀ c₀ : ℝ)
    (hA : 0 ≤ A) (hCq : 0 ≤ Cq) (hH₀ : 0 ≤ H₀) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop,∀ (as : List PositiveMass) (ho : MassOrdered 0 as)
      (q : ℕ→FeatureIndex n→ℝ) (low high : ℕ),low ≤ high → high ≤ as.length →
    ∀ (r W v : ℝ),0<r → 0<W → 0<v → (n:ℝ)^(-(1:ℝ)/6+m) ≤ r →
      OriginalBoundaryPrimitiveInput n k dc dq as q low high B A Cq H₀ c₀ r W v →
      originalBoundaryResamplingMoment n (k+1) as q low high ≤
        (2*(n:ℝ)^(-delta)*savedExteriorScale r W v)^(2*(k+1)) := by
  filter_upwards [eventually_physical_exterior_resampling_from_primitives k dc dq B A Cq H₀ c₀
    hA hCq hH₀ hc₀ hgap] with n hn
  intro as ho q low high hlh hhi r W v hr hW hv hlow I
  let steps := originalBoundaryTailSteps n as q low
  let pre := steps.take (high-low)
  let tail := steps.drop (high-low)
  have hlen : steps.length=(as.drop low).length := length_clockSteps _ _
  have hcut : high-low ≤ steps.length := by rw [hlen,List.length_drop]; omega
  have hpre : pre.length=high-low := List.length_take_of_le hcut
  have hfull : pre++tail=steps := List.take_append_drop _ _
  haveI := originalBoundaryPrefixLaw_probability n as ho q low (hlh.trans hhi)
  have hrawprefix := original_boundary_raw_ratio_le_full n (k+1) as ho q low
    (hlh.trans hhi) I.xspos
  dsimp only at hrawprefix
  rw [←I.actualLowMass] at hrawprefix
  have hraw := (pow_le_pow_left₀
    (zero_le_one.trans (physicalRawRatio_one_le n (k+1) steps I.c I.xs
      (originalBoundaryPrefixLaw n as q low) id measurable_id)) hrawprefix 2).trans I.fullRaw
  have H := hn (FeatureIndex n→ℝ) pre tail I.c I.D₀ I.xs I.H r W v
    I.Dpos I.xspos I.Hnonneg hr hW hv hlow (by simpa only [hfull] using I.ordered)
    (originalBoundaryPrefixLaw n as q low) id measurable_id I.cs I.anchor I.duration
    (by simpa only [hfull,hpre] using I.last)
    (by simpa only [hfull,hpre] using I.ends)
    (by simpa only [hfull,hpre] using I.clocks)
    (by simpa only [hfull,hpre] using I.scales) I.count (by simpa only [hfull] using hraw) I.highAnchor I.innovation
  simpa only [originalBoundaryResamplingMoment,hfull,hpre,steps] using H

theorem eventually_actual_full_boundary_polynomial_from_primitives
    (a dc dq : ℕ) (ha : 0<a) (B A Cq H₀ c₀ : ℝ)
    (hA : 0 ≤ A) (hCq : 0 ≤ Cq) (hH₀ : 0 ≤ H₀) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop,∀ (U : ℕ) (as : List PositiveMass)
      (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
      (b h : ℕ→ℝ),Monotone b → Monotone h → (∀ z,0 ≤ b z) → (∀ z,0 ≤ h z) →
    ∀ (t : ℝ),t ∈ Icc (0:ℝ) 1 →
    ∀ (i j k : Fin a→T.Slot),
      (∀ e,i e ≠ j e) → (∀ e,i e ≠ k e) → (∀ e,j e ≠ k e) →
      (∀ e,T.splitIndex (i e) (j e)=T.splitIndex (i e) (k e)) →
      (∀ e,T.splitIndex (i e) (j e)<T.splitIndex (j e) (k e)) →
      (∀ e,T.splitIndex (i e) (j e) ≤ as.length ∧ T.splitIndex (i e) (j e)<U) →
    ∀ (rho : Fin a→ℝ) (r W xi : ℝ) (v : Fin a→ℝ),
      (∀ e,0<rho e) → 0<r → 0<W → 0<xi → (∀ e,0<v e) →
      ((n+1:ℕ) : ℝ)^(-(1:ℝ)/6+m) ≤ r →
      (∀ e,finitePhysicalLowRawBudget n a as b h (T.splitIndex (i e) (j e)) ≤ (rho e)^(2*a)) →
      (∀ e,OriginalBoundaryPrimitiveInput (n+1) (a-1) dc dq as
        (physicalCompletedClock (n+1) b h) (T.splitIndex (i e) (j e))
        (T.splitIndex (j e) (k e)) B A Cq H₀ c₀ r W (v e)) →
      (∀ e,|b (T.splitIndex (i e) (j e))|^(2*a)*nativeBoundaryRowFactor n T b h*
        (2:ℝ)^(2*a-1)*(nativeBoundaryCompletionFactor n T b*
          (2*((n+1:ℕ) : ℝ)^(-delta)*savedExteriorScale r W (v e))^(2*a)+
          (2/(n+1:ℕ):ℝ)^(2*a)) ≤ (xi*rho e)^(2*a)) →
      T.disorderExpect (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavityVariance n U as b h t)
        (fun σ=>(fullBoundaryAffineProduct n
          (fun e=>h (T.splitIndex (i e) (j e))) (fun e=>b (T.splitIndex (i e) (j e)))
            (fun e=>T.atSlot σ (j e)) (fun e=>T.atSlot σ (i e))-
          fullBoundaryAffineProduct n
          (fun e=>h (T.splitIndex (i e) (j e))) (fun e=>b (T.splitIndex (i e) (j e)))
            (fun e=>T.atSlot σ (k e)) (fun e=>T.atSlot σ (i e)))^2) 0 ≤
        ((a:ℝ)*xi*(∏ e,rho e))^2 := by
  have HE := (tendsto_add_atTop_nat 1).eventually
    (eventually_original_boundary_resampling_from_primitives (a-1) dc dq B A Cq H₀ c₀
      hA hCq hH₀ hc₀ hgap)
  filter_upwards [HE] with n hn
  intro U as T ho b h hb hh hb0 hh0 t ht i j k hij hik hjk hlow hgap' hcut
    rho r W xi v hrho hr hW hxi hv hrscale hraw I hdom
  apply actual_full_boundary_polynomial_from_physical_resampling n U T ho b h hb hh hb0 hh0
    ht ha i j k hij hik hjk hlow hgap' hcut rho hrho hxi hraw
  intro e
  have he := hn as ho (physicalCompletedClock (n+1) b h)
    (T.splitIndex (i e) (j e)) (T.splitIndex (j e) (k e)) (hgap' e).le
    (T.splitIndex_le_clockLength _ _) r W (v e) hr hW (hv e) hrscale (I e)
  have ha' : a-1+1=a := by omega
  rw [ha'] at he
  apply le_trans _ (hdom e)
  unfold nativeBoundaryReplacementBudget
  gcongr <;> simp only [nativeBoundaryRowFactor,nativeBoundaryCompletionFactor] <;> positivity

end OAI.SKFluctuations.Cavity
