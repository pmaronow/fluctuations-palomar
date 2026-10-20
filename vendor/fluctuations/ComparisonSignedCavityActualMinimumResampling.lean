module

public import ComparisonSignedCavityActualBoundarySchedule
public import ComparisonSignedCavityEarlierCenterResampling
public import ComparisonTwoSidedNativeRawRetention
public import ComparisonTwoSidedNativeReverseMovement
public import ComparisonNativeOverlapRawAmplitude

@[expose] public section

noncomputable section
set_option maxHeartbeats 4500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy Cavity

def subtractBoundaryPrefix (cs : List (ℝ×ℕ)) (low : ℕ) : List (ℝ×ℕ) :=
  cs.map (fun p=>(p.1,p.2-low))

@[simp] theorem subtractBoundaryPrefix_length (cs : List (ℝ×ℕ)) (low : ℕ) :
    (subtractBoundaryPrefix cs low).length=cs.length := List.length_map _

@[simp] theorem subtractBoundaryPrefix_get (cs : List (ℝ×ℕ)) (low : ℕ)
    (j : Fin (subtractBoundaryPrefix cs low).length) :
    (subtractBoundaryPrefix cs low).get j =
      ((cs.get (Fin.cast (subtractBoundaryPrefix_length cs low) j)).1,
        (cs.get (Fin.cast (subtractBoundaryPrefix_length cs low) j)).2-low) := by
  induction cs with
  | nil => exact Fin.elim0 j
  | cons p cs ih =>
    refine Fin.cases ?_ (fun j=>?_) j
    · rfl
    · exact ih j

theorem lastLayerCut_subtractBoundaryPrefix (cs : List (ℝ×ℕ)) (low t : ℕ) :
    lastLayerCut (subtractBoundaryPrefix cs low) (t-low)=lastLayerCut cs t-low := by
  induction cs generalizing t with
  | nil => rfl
  | cons p cs ih => exact ih p.2

theorem cutPredecessor_subtractBoundaryPrefix (cs : List (ℝ×ℕ)) (low t : ℕ)
    (j : Fin (subtractBoundaryPrefix cs low).length) :
    cutPredecessor (subtractBoundaryPrefix cs low) (t-low) j=
      cutPredecessor cs t (Fin.cast (subtractBoundaryPrefix_length cs low) j)-low := by
  induction cs generalizing t with
  | nil => exact Fin.elim0 j
  | cons p cs ih =>
    refine Fin.cases ?_ (fun j=>?_) j
    · rfl
    · exact ih p.2 j

theorem overlapComponentEnd_subtractBoundaryPrefix (cs : List (ℝ×ℕ)) (low t : ℕ)
    (i : Fin ((subtractBoundaryPrefix cs low).length+1)) :
    overlapComponentEnd (subtractBoundaryPrefix cs low) (t-low) i=
      overlapComponentEnd cs t
        (Fin.cast (congrArg (fun z=>z+1) (subtractBoundaryPrefix_length cs low)) i)-low := by
  refine Fin.cases ?_ (fun j=>?_) i
  · rfl
  · change ((subtractBoundaryPrefix cs low).get j).2 = _
    rw [subtractBoundaryPrefix_get]
    congr 1

theorem physical_projection_clock_fork_le_start {n : ℕ}
    {steps : List (GaussianStep (FeatureIndex n))} {fork v w : ℕ} {a D : ℝ}
    (hc : PhysicalProjectionClock n steps fork v w a D) : fork ≤ v ∧ v ≤ w := by
  cases hc <;> simp only [List.length_append] <;> omega

theorem sampled_clockSteps_native (n : ℕ) (q : ℝ→FeatureIndex n→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let steps := sampleClockSteps q 0 as
    let Q := stepClockValues (fun i=>(q 0 i:ℝ)) steps
    clockSteps as (cumulativeIncrements (Q 0) (fun j=>Q (j+1)))=steps := by
  dsimp only
  have hs := sampleClockSteps_ordered q as ho
  have hpos : ∀ st∈sampleClockSteps q 0 as,0<st.1 := fun st hst=>hs.mem_pos st hst
  have hmass (xs : List PositiveMass) (a : ℝ)
      (hp : ∀ st∈sampleClockSteps q a xs,0<st.1) :
      positiveStepMasses (sampleClockSteps q a xs) hp=xs := by
    induction xs generalizing a with
    | nil => rfl
    | cons m xs ih =>
        simp only [sampleClockSteps,positiveStepMasses,List.cons.injEq]
        constructor
        · trivial
        · exact ih m.val _
  have H := clockSteps_stepClockValues (fun i=>(q 0 i:ℝ)) (sampleClockSteps q 0 as) hpos
  rw [hmass as 0 hpos] at H
  simpa only [stepClockValues_zero] using H

theorem original_boundary_raw_ratio_le_sampled (n l : ℕ)
    (q : ℝ→FeatureIndex n→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (low : ℕ) (hlow : low ≤ as.length) {xs : ℝ} (hxs : 0<xs) :
    let steps := sampleClockSteps q 0 as
    let Q := stepClockValues (fun i=>(q 0 i:ℝ)) steps
    physicalRawRatio n l (originalBoundaryTailSteps n as Q low)
      (physicalCutMass 0 steps low) xs (originalBoundaryPrefixLaw n as Q low) id measurable_id ≤
      physicalRawRatio n l steps 0 xs (Measure.pi (fun i=>gaussianReal 0 (q 0 i))) id measurable_id := by
  dsimp only
  have H := original_boundary_raw_ratio_le_full n l as ho
    (stepClockValues (fun i=>(q 0 i:ℝ)) (sampleClockSteps q 0 as)) low hlow hxs
  dsimp only at H
  rw [sampled_clockSteps_native n q as ho] at H
  simpa only [stepClockValues_zero,Real.toNNReal_coe] using H

theorem originalBoundaryTailSteps_eq_drop (n : ℕ) (as : List PositiveMass)
    (q : ℕ→FeatureIndex n→ℝ) (low : ℕ) (hlow : low ≤ as.length) :
    originalBoundaryTailSteps n as q low =
      (clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1)))).drop low := by
  have H := clockSteps_take_drop as (cumulativeIncrements (q 0) (fun j=>q (j+1))) low hlow
  have hlen : (clockSteps (as.take low) (cumulativeIncrements (q 0) (fun j=>q (j+1)))).length=low := by
    rw [length_clockSteps,List.length_take_of_le hlow]
  have hd : (clockSteps (as.take low) (cumulativeIncrements (q 0) (fun j=>q (j+1)))).drop low=[] := by
    exact List.drop_eq_nil_iff.mpr (by omega)
  rw [H,List.drop_append_of_le_length (by omega),hd,List.nil_append]
  rfl

theorem physicalCutMass_drop_boundary {ι : Type}
    (steps : List (GaussianStep ι)) (c : ℝ) (low cut : ℕ) (hlow : low ≤ cut) :
    physicalCutMass (physicalCutMass c steps low) (steps.drop low) (cut-low)=
      physicalCutMass c steps cut := by
  induction steps generalizing c low cut with
  | nil =>
      cases low with
      | zero => rfl
      | succ low =>
        cases cut with
        | zero => omega
        | succ cut =>
          simp only [physicalCutMass,List.drop_nil,Nat.add_sub_add_right]
          cases cut-low <;> rfl
  | cons st steps ih =>
    cases low with
    | zero => rfl
    | succ low =>
      cases cut with
      | zero => omega
      | succ cut =>
          simpa only [physicalCutMass,List.drop_succ_cons,Nat.add_sub_add_right] using
            (ih st.1 low cut (by omega))

theorem original_boundary_projection_schedule_transport (n : ℕ)
    (as : List PositiveMass) (q : ℕ→FeatureIndex n→ℝ)
    (low t : ℕ) (hlow : low ≤ as.length) (hlt : low ≤ t)
    (cs : List (ℝ×ℕ)) (a D : Fin cs.length→ℝ) {D₀ xs H B : ℝ}
    (hlast : lastLayerCut cs t=
      (clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1)))).length+1)
    (hends : ∀ j : Fin cs.length,cutPredecessor cs t j ≤ (cs.get j).2 ∧
      (cs.get j).2 ≤ (clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1)))).length+1)
    (hclocks : ∀ j,0<a j ∧ D₀ ≤ D j ∧ D j ≤ B ∧
      PhysicalProjectionClock n (clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1))))
        low (cutPredecessor cs t j) (cs.get j).2 (a j) (D j))
    (hscales : ∀ i j,i ≤ j.succ →
      xs+physicalCutMass 0 (clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1))))
        (overlapComponentEnd cs t i) ≤ H*(a j)^2) :
    let cs' := subtractBoundaryPrefix cs low
    let a' := fun j : Fin cs'.length=>a (Fin.cast (subtractBoundaryPrefix_length cs low) j)
    let D' := fun j : Fin cs'.length=>D (Fin.cast (subtractBoundaryPrefix_length cs low) j)
    let c := physicalCutMass 0 (clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1)))) low
    lastLayerCut cs' (t-low)=(originalBoundaryTailSteps n as q low).length+1 ∧
      (∀ j : Fin cs'.length,cutPredecessor cs' (t-low) j ≤ (cs'.get j).2 ∧
        (cs'.get j).2 ≤ (originalBoundaryTailSteps n as q low).length+1) ∧
      (∀ j,0<a' j ∧ D₀ ≤ D' j ∧ D' j ≤ B ∧
        PhysicalProjectionClock n (originalBoundaryTailSteps n as q low) 0
          (cutPredecessor cs' (t-low) j) (cs'.get j).2 (a' j) (D' j)) ∧
      (∀ i j,i ≤ j.succ → xs+physicalCutMass c (originalBoundaryTailSteps n as q low)
        (overlapComponentEnd cs' (t-low) i) ≤ H*(a' j)^2) ∧
      (physicalOverlapResidualPairs cs').card=(physicalOverlapResidualPairs cs).card := by
  dsimp only
  let steps := clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1)))
  have hlen : steps.length=as.length := length_clockSteps _ _
  rw [originalBoundaryTailSteps_eq_drop n as q low hlow]
  have htail : (steps.drop low).length+1=steps.length+1-low := by
    rw [List.length_drop]; omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [lastLayerCut_subtractBoundaryPrefix,hlast]
    exact htail.symm
  · intro j
    rw [cutPredecessor_subtractBoundaryPrefix,subtractBoundaryPrefix_get]
    have H := hends (Fin.cast (subtractBoundaryPrefix_length cs low) j)
    change _ ∧ (cs.get (Fin.cast (subtractBoundaryPrefix_length cs low) j)).2 ≤ steps.length+1 at H
    constructor
    · omega
    · change _ ≤ (steps.drop low).length+1
      rw [htail]
      omega
  · intro j
    obtain ⟨ha,hD,hDB,hclock⟩ := hclocks (Fin.cast (subtractBoundaryPrefix_length cs low) j)
    refine ⟨ha,hD,hDB,?_⟩
    have H := actual_physical_projection_clock_suffix hclock
    simpa only [cutPredecessor_subtractBoundaryPrefix,subtractBoundaryPrefix_get] using H
  · intro i j hij
    rw [overlapComponentEnd_subtractBoundaryPrefix]
    let i' := Fin.cast (congrArg (fun z=>z+1) (subtractBoundaryPrefix_length cs low)) i
    let j' := Fin.cast (subtractBoundaryPrefix_length cs low) j
    have hi : low ≤ overlapComponentEnd cs t i' := by
      refine Fin.cases ?_ (fun z=>?_) i'
      · exact hlt
      · exact (physical_projection_clock_fork_le_start (hclocks z).2.2.2).1.trans (hends z).1
    rw [physicalCutMass_drop_boundary steps 0 low _ hi]
    apply hscales i' j'
    change i.val ≤ j.val+1
    exact hij
  · simp [physicalOverlapResidualPairs]

end OAI.SKFluctuations

namespace OAI.SKFluctuations
open Hierarchy Cavity

theorem eventually_original_boundary_resampling_from_full_schedule
    (k dc dq : ℕ) (B A Cq H₀ c₀ : ℝ)
    (hA : 0≤A) (hCq : 0≤Cq) (hH₀ : 0≤H₀) (hc₀ : 0<c₀)
    {m eta : ℝ} (hgap : 2*eta<6*m) :
    ∀ᶠ n : ℕ in atTop,∀ (as : List PositiveMass) (_ho : MassOrdered 0 as)
      (q : ℕ→FeatureIndex n→ℝ) (low high t : ℕ),low ≤ t → t ≤ high → high ≤ as.length →
    ∀ (D₀ xs H r W v : ℝ),0<D₀ → 0<xs → 0≤H → 0<r → 0<W → 0<v →
      (n:ℝ)^(-(1:ℝ)/6+m) ≤ r →
    ∀ (cs : List (ℝ×ℕ)) (a D : Fin cs.length→ℝ),
      let steps := clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1)))
      lastLayerCut cs t=steps.length+1 →
      (∀ j : Fin cs.length,cutPredecessor cs t j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) →
      (∀ j,0<a j ∧ D₀ ≤ D j ∧ D j ≤ B ∧
        PhysicalProjectionClock n steps low (cutPredecessor cs t j) (cs.get j).2 (a j) (D j)) →
      (∀ i j,i ≤ j.succ → xs+physicalCutMass 0 steps (overlapComponentEnd cs t i) ≤ H*(a j)^2) →
      ((physicalOverlapResidualPairs cs).card:ℝ)^2 ≤ A*(Real.log (n:ℝ))^dc →
      (physicalRawRatio n (k+1) steps 0 xs
        (Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))) id measurable_id)^2 ≤
        Cq*(Real.log (n:ℝ))^dq →
      H ≤ H₀/v → c₀*W^3/Real.log (n:ℝ) ≤ D₀ →
      originalBoundaryResamplingMoment n (k+1) as q low high ≤
        (2*(n:ℝ)^(-eta)*savedExteriorScale r W v)^(2*(k+1)) := by
  let C := 4*(projectionLpConstant k)^2*A*Cq*H₀/c₀
  filter_upwards [eventually_physical_projection_error_polynomial k (dc+dq+5) B C hgap,
    eventually_gt_atTop (1:ℕ)] with n hn hnpos
  intro as ho q low high t hlt hth hhigh D₀ xs H r W v hD₀ hxs hH hr hW hv hrscale
    cs a D stepsOrig hlast hends hclocks hscales hcount hraw hanchor hduration
  let steps := clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1)))
  let ts := originalBoundaryTailSteps n as q low
  let c := physicalCutMass 0 steps low
  let cs' := subtractBoundaryPrefix cs low
  let a' := fun j : Fin cs'.length=>a (Fin.cast (subtractBoundaryPrefix_length cs low) j)
  let D' := fun j : Fin cs'.length=>D (Fin.cast (subtractBoundaryPrefix_length cs low) j)
  have hlo : low ≤ as.length := hlt.trans (hth.trans hhigh)
  obtain ⟨hlast',hends',hclocks',hscales',hcard⟩ := original_boundary_projection_schedule_transport
    n as q low t hlo hlt cs a D hlast hends hclocks hscales
  dsimp only at hlast' hends' hclocks' hscales' hcard
  have hlen : ts.length=as.length-low := by simp only [ts,originalBoundaryTailSteps,length_clockSteps,List.length_drop]
  have ht : t-low ≤ ts.length+1 := by rw [hlen]; omega
  have hs : OrderedSteps c ts := by
    change OrderedSteps c (originalBoundaryTailSteps n as q low)
    rw [originalBoundaryTailSteps_eq_drop n as q low hlo]
    exact orderedSteps_drop_cutMass steps (clockSteps_ordered ho _) low
  have := originalBoundaryPrefixLaw_probability n as ho q low hlo
  have hrawprefix := original_boundary_raw_ratio_le_full n (k+1) as ho q low hlo hxs
  dsimp only at hrawprefix
  have hraw' : (physicalRawRatio n (k+1) ts c xs (originalBoundaryPrefixLaw n as q low) id measurable_id)^2 ≤
      Cq*(Real.log (n:ℝ))^dq := by
    apply (pow_le_pow_left₀ (zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)) hrawprefix 2).trans hraw
  have hN : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hL : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hnpos)
  have hbase : ((physicalOverlapResidualPairs cs').card:ℝ)^2 *
      (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4 *
        (physicalRawRatio n (k+1) ts c xs (originalBoundaryPrefixLaw n as q low) id measurable_id)^2*H/((n:ℝ)*D₀)) ≤
      C*(Real.log (n:ℝ))^(dc+dq+5)*(n:ℝ)^(-(6*m))*savedExteriorScale r W v^2 := by
    have hc' : ((physicalOverlapResidualPairs cs').card:ℝ)^2 ≤ A*(Real.log (n:ℝ))^dc := by
      simpa only [cs',hcard] using hcount
    have Hcoef := resampling_coefficient_from_primitives dc dq (P:=projectionLpConstant k)
      hN hL hD₀ hc₀ hW hv hA hCq hH₀ hH hc' hraw' hanchor hduration
    apply Hcoef.trans
    rw [resampling_coefficient_scale (dc+dq+5) hN hr hW hv]
    have Hsmall := reciprocal_sixth_small_scale hN hr hrscale
    have Hmul := mul_le_mul_of_nonneg_left Hsmall
      (show 0≤C*(Real.log (n:ℝ))^(dc+dq+5) by dsimp [C]; positivity)
    simpa only [C,div_eq_mul_inv,mul_assoc,one_mul,neg_mul] using
      mul_le_mul_of_nonneg_right Hmul (sq_nonneg (savedExteriorScale r W v))
  have Hproj := hn (FeatureIndex n→ℝ) ts c D₀ xs H (savedExteriorScale r W v)
    hD₀ hxs hH hs (originalBoundaryPrefixLaw n as q low) id measurable_id cs' 0 (t-low) a' D'
    ht hlast' hends' hclocks' hscales' hbase
  have Hres := physical_exterior_resampling_moment_le_earlier_center n (k+1) (Nat.succ_pos k)
    ts hs (originalBoundaryPrefixLaw n as q low) id measurable_id
    (t:=t-low) (k:=high-low) (by omega)
  apply Hres.trans
  calc
    _ ≤ (2:ℝ)^(2*(k+1))*(((n:ℝ)^(-eta)*savedExteriorScale r W v)^(2*(k+1))) :=
      mul_le_mul_of_nonneg_left Hproj (by positivity)
    _ = _ := by rw [←mul_pow]; congr 1; ring

end OAI.SKFluctuations

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity

theorem eventually_native_minimum_original_boundary_raw
    (ell : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀ (u : PositiveMass),u.val ≤ 1 →
      ∀ (extra : List PositiveMass),(∀v∈extra,v.val ≤ 1) →
      ∃ us : List PositiveMass,(∀v∈us,v.val ≤ 1) ∧ u∈us ∧ (∀v∈extra,v∈us) ∧
        ∀ᶠ j : ℕ in atTop,
          let as := finiteCutMasses us j
          let steps := sampleClockSteps (completedPathClock n a.bf a.hf) 0 as
          let Q := stepClockValues (fun i=>(completedPathClock n a.bf a.hf 0 i:ℝ)) steps
          (physicalRawRatio n (ell+1) steps 0 a.xs
            (Measure.pi fun i=>gaussianReal 0 (completedPathClock n a.bf a.hf 0 i)) id measurable_id)^2 ≤ 2*C ∧
          ∀ low : ℕ,low ≤ as.length →
            (physicalRawRatio n (ell+1) (originalBoundaryTailSteps n as Q low)
              (physicalCutMass 0 steps low) a.xs (originalBoundaryPrefixLaw n as Q low)
              id measurable_id)^2 ≤ 2*C := by
  obtain ⟨C,hC,hraw⟩ := comparison_minimum_finite_raw_ratio_retaining
    (D:=D) ell Bclock hm hdelta hroom hcl hcu hAz (by norm_num : (0:ℝ)<1/3) hC0 hCt
  have hlog : ∀ᶠ n : ℕ in atTop,1≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  refine ⟨C,hC,?_⟩
  filter_upwards [hraw,eventually_comparisonLowerScale_depth hC0 hm,hlog,eventually_ge_atTop (1:ℕ)]
    with n hnraw hndepth hnlog hn1
  intro a u hu extra hextra
  let c := a.context
  have hN1 : (1:ℝ)≤c.N := by exact_mod_cast hn1
  have hnd : 1/c.N≤c.d := by
    have H := hndepth c.E c.d c.hE c.hd a.hlower
    have hs : comparisonLowerScale n c.E c.d≤c.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ c.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact H.trans hs
  let g := laplaceComparisonStrength c.d a.lam
  let hg := (laplaceComparisonStrength_contDiff c.d a.lam).continuous
  let ie := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one c.hc c.hk c.hkc c.hm c.hM g hg a.alpha)
  let iq := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one c.hc c.hk c.hkc c.hm c.hM (fun r=>g r*r)
      (hg.mul continuous_id) a.alpha)
  let bi := fun v=>(a.b v-ie v).toNNReal
  let hi := fun v=>(a.h v+iq v).toNNReal
  have had beta := comparisonVariableEndpoint_inverse_clocks_admissible c.hc c.hk c.hkc c.hm c.hM
    a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 beta
  have hmin : ∀beta:c.Profile,
      inverseCompensatedPressure zero_le_one zero_le_one c.hc c.hk c.hkc c.hm c.hM
        g hg n a.b a.h 0 a.alpha ≤
      inverseCompensatedPressure zero_le_one zero_le_one c.hc c.hk c.hkc c.hm c.hM
        g hg n a.b a.h 0 beta := by
    intro beta
    have H := a.minimum beta
    rw [comparisonVariableEndpointObjective_eq_inverse c.hc c.hk c.hkc c.hm c.hM n c.hn
      a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha,
      comparisonVariableEndpointObjective_eq_inverse c.hc c.hk c.hkc c.hm c.hM n c.hn
      a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 beta] at H
    exact H
  have hslow : ∀r∈Icc a.z 1,(1/3)/Real.log (n:ℝ)≤1-comparisonLogSlope g r := by
    intro r hr
    exact laplaceComparisonStrength_uniform_slope hN1 hnlog c.hd hnd a.hlam a.hld
      (Icc_subset_Icc a.hz.1 le_rfl hr)
  have hclock : (hi 1:ℝ)-(hi 0:ℝ)≤Bclock := by
    dsimp [hi,iq]
    rw [fullMassCoefficient_eq_sweepQuantile c.hc c.hk c.hkc c.hm c.hM _ _ a.alpha
        (show (1:ℝ)∈Icc (0:ℝ) 1 by simp),
      fullMassCoefficient_eq_sweepQuantile c.hc c.hk c.hkc c.hm c.hM _ _ a.alpha
        (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)]
    exact a.clockBudget
  obtain ⟨us,hus,huus,hextraus,hfinite⟩ := hnraw c.hn c.hE c.hd
    (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/4))
    (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/4)) g a.alpha
    (laplaceComparisonStrength_contDiff _ _) (fun r _=>laplaceComparisonStrength_pos c.d a.hlam r)
    (fun r _=>by
      have hp:=laplaceComparisonStrength_logSlope_mem c.hd.ne' a.hlam.ne' r
      exact ⟨hp.1,hp.2.le⟩)
    a.b a.h (fun beta=>(had beta).1) (fun beta=>(had beta).2.1)
    (fun beta=>(had beta).2.2.1) (fun beta=>(had beta).2.2.2) hmin u hu extra hextra a.xs a.z
    a.hxs a.hscale a.hxs.le c.hU.le a.hz a.hzxs a.hdD a.hupper a.hlower a.htest
    a.regular hslow a.hh hclock
  refine ⟨us,hus,huus,hextraus,?_⟩
  filter_upwards [hfinite] with j hj
  dsimp only at hj ⊢
  have ho := finiteCutMasses_ordered us hus j
  have heq := comparisonVariableEndpoint_sampled_clocks_eq c.hc c.hk c.hkc c.hm c.hM
    n a.b a.h g hg a.alpha (finiteCutMasses us j) ho
  dsimp only at heq
  change (physicalRawRatio n (ell+1) (sampleClockSteps (completedPathClock n bi hi) 0 (finiteCutMasses us j))
    0 a.xs (Measure.pi fun i=>gaussianReal 0 (completedPathClock n bi hi 0 i)) id measurable_id)^2 ≤ 2*C at hj
  have hjnative : (physicalRawRatio n (ell+1)
      (sampleClockSteps (completedPathClock n a.bf a.hf) 0 (finiteCutMasses us j)) 0 a.xs
      (Measure.pi fun i=>gaussianReal 0 (completedPathClock n a.bf a.hf 0 i)) id measurable_id)^2 ≤ 2*C := by
    dsimp only [bi,hi,ie,iq] at hj
    rw [heq.1,heq.2] at hj
    exact hj
  refine ⟨hjnative,?_⟩
  intro low hlow
  have H := original_boundary_raw_ratio_le_sampled n (ell+1)
    (completedPathClock n a.bf a.hf) (finiteCutMasses us j) ho low hlow a.hxs
  dsimp only at H
  apply (pow_le_pow_left₀ ?_ H 2).trans hjnative
  exact zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)

theorem eventually_native_minimum_original_boundary_resampling
    (ell : ℕ) (Bclock ce Rmacro F exponent : ℝ)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hce : 0<ce) (hmacro : 0<Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀ (u : PositiveMass),u.val ≤ 1 →
      ∀ (extra : List PositiveMass),(∀v∈extra,v.val ≤ 1) →
      ∃ us : List PositiveMass,(∀v∈us,v.val ≤ 1) ∧ u∈us ∧ (∀v∈extra,v∈us) ∧
        ∀ᶠ j : ℕ in atTop,
          let as := finiteCutMasses us j
          let steps := sampleClockSteps (completedPathClock n a.bf a.hf) 0 as
          let Q := stepClockValues (fun i=>(completedPathClock n a.bf a.hf 0 i:ℝ)) steps
          ∀ (s W r : ℝ) (low high : ℕ),0<s → 0<W → 0<r →
            W ≤ s → a.xs ≤ s → a.z ≤ s/2 → 2*s ≤ Rmacro →
            (n:ℝ)^(-exponent) ≤ s → (n:ℝ)^(-(1:ℝ)/6+m) ≤ r →
            ce*W^2 ≤ laplaceComparisonStrength a.context.d a.lam W →
            high ≤ as.length → a.R (partitionPoint 0 as low) ≤ s/2 →
            a.R (partitionPoint 0 as high)=4*s →
            originalBoundaryResamplingMoment n (ell+1) as Q low high ≤
              (2*(n:ℝ)^(-eta)*savedExteriorScale r W (partitionPoint 0 as high))^(2*(ell+1)) := by
  obtain ⟨C,hC,hraw⟩ := eventually_native_minimum_original_boundary_raw
    ell Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let A := (exponent/Real.log 2+4)^4
  let H₀ := 4*cu*F/(cl/8)^2
  have hF : 0≤F := by linarith
  have hH₀ : 0≤H₀ := by dsimp [H₀]; positivity
  have hsave := eventually_original_boundary_resampling_from_full_schedule ell 4 0 Bclock A (2*C) H₀ (ce/24)
    (by dsimp [A]; positivity) (by positivity) hH₀ (by positivity) hgap
  have hlog : ∀ᶠ n : ℕ in atTop,1≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hraw,hsave,eventually_comparisonLowerScale_depth hC0 hm,hlog,eventually_gt_atTop (1:ℕ)]
    with n hnraw hnsave hndepth hnlog hn1
  intro a u hu extra hextra
  let c := a.context
  have hN1 : (1:ℝ)≤c.N := by exact_mod_cast hn1.le
  have hNgt : 1<c.N := by exact_mod_cast hn1
  have hnd : 1/c.N≤c.d := by
    have H := hndepth c.E c.d c.hE c.hd a.hlower
    have H' : comparisonLowerScale n c.E c.d≤c.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ c.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact H.trans H'
  obtain ⟨us,hus,huus,hextraus,hfinite⟩ := hnraw a u hu extra hextra
  have hmesh : ∀ᶠ j : ℕ in atTop,(((j+1:ℕ):ℝ)⁻¹)/c.floor ≤ c.N^(-exponent)/16 := by
    apply ((uniformMasses_mesh_tendsto.div_const c.floor).eventually
      (gt_mem_nhds (show 0/c.floor<c.N^(-exponent)/16 by simpa only [zero_div] using
        (show 0<c.N^(-exponent)/16 by positivity)))).mono
    intro j hj
    simpa using hj.le
  refine ⟨us,hus,huus,hextraus,?_⟩
  filter_upwards [hfinite,hmesh] with j hj hmj
  dsimp only at hj ⊢
  intro s W r low high hs hW hr hWs hxss hzs hsR hslow hrscale hstrength hhigh hlow hhighradius
  have ho := finiteCutMasses_ordered us hus j
  have hend := finiteCutMasses_end us hus j
  have hpart := finiteCutMasses_mesh us hus j
  have hmeshnonneg : 0≤(((j+1:ℕ):ℝ)⁻¹) := by positivity
  have hsmall : (((j+1:ℕ):ℝ)⁻¹)/c.floor ≤ s/16 := hmj.trans (by linarith)
  have hregular : ∀v∈Icc (s/2) 1,cl*v ≤ a.alpha.val.val v ∧ a.alpha.val.val v ≤ cu*v :=
    fun v hv=>a.regular v (Icc_subset_Icc hzs le_rfl hv)
  obtain ⟨J,hJ,hJmacro,hJone,hJlog⟩ := exists_actual_boundary_dyadic_count hNgt hnlog hs hmacro hsR hRhalf hslow
  obtain ⟨cs,t,anchor,duration,hlen,hlt,hth,htlen,hlast,hends,hclocks,hscales,hcount,hDpos⟩ :=
    exists_actual_comparison_boundary_projection_schedule n c.hn c.hc c.hk c.hkc c.hm c.hM
      a.alpha a.b a.h a.hb a.hlb a.hh a.hh0 hN1 hnlog c.hd hnd a.hlam a.hld
      (finiteCutMasses us j) ho hend hmeshnonneg hpart hs hsmall hW hWs hce hstrength
      hcl hcu.le hmacro hFmass hFradius a.hxs.le hxss hregular hJ hJmacro hJone hhigh hlow
      (by change 2*s ≤ a.R (partitionPoint 0 (finiteCutMasses us j) high); rw [hhighradius]; linarith)
      a.clockBudget
  have hmass := actual_comparison_boundary_schedule_high_anchor c.hc c.hk c.hkc c.hm c.hM
    a.alpha (finiteCutMasses us j) ho hs hcl hF hhighradius hregular
  have hcount' : ((physicalOverlapResidualPairs cs).card:ℝ)^2 ≤ A*(Real.log (n:ℝ))^4 := by
    apply hcount.trans
    have H := pow_le_pow_left₀ (Nat.cast_nonneg (J+3)) hJlog 4
    simpa only [mul_pow,A] using H
  let steps := sampleClockSteps (completedPathClock n a.bf a.hf) 0 (finiteCutMasses us j)
  let Q := stepClockValues (fun i=>(completedPathClock n a.bf a.hf 0 i:ℝ)) steps
  have heq : clockSteps (finiteCutMasses us j) (cumulativeIncrements (Q 0) (fun z=>Q (z+1)))=steps :=
    sampled_clockSteps_native n (completedPathClock n a.bf a.hf) (finiteCutMasses us j) ho
  apply hnsave (finiteCutMasses us j) ho Q low high t hlt hth hhigh
    (ce*W^3/(24*Real.log (n:ℝ))) a.xs (F/((cl/8)^2*s)) r W (partitionPoint 0 (finiteCutMasses us j) high)
    hDpos a.hxs (by positivity) hr hW hmass.1 hrscale cs anchor duration
  · simpa only [heq,steps] using hlast
  · simpa only [heq,steps] using hends
  · simpa only [heq,steps] using hclocks
  · simpa only [heq,steps] using hscales
  · exact hcount'
  · rw [heq]
    simpa only [Q,stepClockValues_zero,Real.toNNReal_coe,pow_zero,mul_one,steps] using hj.1
  · exact hmass.2
  · ring_nf
    exact le_rfl

theorem native_minimum_original_boundary_critical_radius
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} (hC0 : 0<C0)
    (a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) :
    (n:ℝ)^(-(1:ℝ)/6+m) ≤ C0*a.xs := by
  have hN := a.context.hN
  have hsqrt : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hN
  have he : Real.sqrt (n:ℝ)*(n:ℝ)^(-(2:ℝ)/3+m)=(n:ℝ)^(-(1:ℝ)/6+m) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hN]
    congr 1
    ring
  have H := mul_le_mul_of_nonneg_left a.hlower hsqrt.le
  have H' : (n:ℝ)^(-(1:ℝ)/6+m)*a.context.d ≤ C0*(Real.sqrt (n:ℝ)*a.context.E) := by
    rw [←he]
    nlinarith [H]
  have Hscale : (n:ℝ)^(-(1:ℝ)/6+m) ≤ C0*comparisonLowerScale n a.context.E a.context.d := by
    unfold comparisonLowerScale
    rw [←mul_div_assoc]
    exact (le_div_iff₀ a.context.hd).mpr H'
  exact Hscale.trans (mul_le_mul_of_nonneg_left a.hscale hC0.le)

theorem eventually_native_minimum_calibrated_original_boundary_resampling
    (ell : ℕ) (Bclock Ccal Rmacro F : ℝ)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCcal : 1≤Ccal) (hmacro : 0<Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      a.xs^2 ≤ Ccal^2*laplaceComparisonStrength a.context.d a.lam a.xs →
      ∀ (u : PositiveMass),u.val ≤ 1 →
      ∀ (extra : List PositiveMass),(∀v∈extra,v.val ≤ 1) →
      ∃ us : List PositiveMass,(∀v∈us,v.val ≤ 1) ∧ u∈us ∧ (∀v∈extra,v∈us) ∧
        ∀ᶠ j : ℕ in atTop,
          let as := finiteCutMasses us j
          let steps := sampleClockSteps (completedPathClock n a.bf a.hf) 0 as
          let Q := stepClockValues (fun i=>(completedPathClock n a.bf a.hf 0 i:ℝ)) steps
          let W := max a.xs (Real.sqrt (laplaceComparisonStrength a.context.d a.lam a.xs))
          ∀ (s : ℝ) (low high : ℕ),0<s → W ≤ s → a.z ≤ s/2 → 2*s ≤ Rmacro →
            high ≤ as.length → a.R (partitionPoint 0 as low) ≤ s/2 →
            a.R (partitionPoint 0 as high)=4*s →
            originalBoundaryResamplingMoment n (ell+1) as Q low high ≤
              (2*(n:ℝ)^(-eta)*savedExteriorScale (C0*a.xs) W (partitionPoint 0 as high))^(2*(ell+1)) := by
  have hCcalpos : 0<Ccal := zero_lt_one.trans_le hCcal
  have hsave := eventually_native_minimum_original_boundary_resampling (D:=D) ell Bclock (1/Ccal^3) Rmacro F (1/6)
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt (by positivity) hmacro hRhalf hFmass hFradius
  have hpower : ∀ᶠ n : ℕ in atTop,C0 ≤ (n:ℝ)^m :=
    ((tendsto_rpow_atTop hm).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop C0)
  filter_upwards [hsave,hpower,eventually_gt_atTop (0:ℕ)] with n hn hp hn0
  intro a hcompare u hu extra hextra
  obtain ⟨us,hus,huus,hextraus,hfinite⟩ := hn a u hu extra hextra
  have hcritical := native_minimum_original_boundary_critical_radius hC0 a
  have hN : 0<(n:ℝ) := by exact_mod_cast hn0
  have hxscrit : (n:ℝ)^(-(1:ℝ)/6) ≤ a.xs := by
    have H := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hN.le (-(1:ℝ)/6))
    rw [←Real.rpow_add hN] at H
    have he : m+(-(1:ℝ)/6)=-(1:ℝ)/6+m := by ring
    rw [he] at H
    exact (mul_le_mul_iff_right₀ hC0).mp (by simpa only [mul_comm] using H.trans hcritical)
  obtain ⟨hW,hWd,hstrength⟩ := actual_direct_test_calibration_strength a.context.hd a.hlam a.hld
    a.hxs hCcal hcompare
  refine ⟨us,hus,huus,hextraus,?_⟩
  filter_upwards [hfinite] with j hj
  dsimp only at hj ⊢
  intro s low high hs hWs hzs hsR hhigh hlow hhighradius
  have hxss : a.xs ≤ s := (le_max_left _ _).trans hWs
  exact hj s _ (C0*a.xs) low high hs hW (mul_pos hC0 a.hxs) hWs hxss hzs hsR
    (by simpa only [neg_div] using hxscrit.trans hxss) hcritical hstrength hhigh hlow hhighradius

end OAI.SKFluctuations.LaplaceWindowFormalization
