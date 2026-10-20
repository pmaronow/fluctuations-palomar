module

public import ComparisonSignedCavityObservedRestInnovation

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_sampled_field_duration_take_eq_completed (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (i : Fin n) (j : ℕ) :
    physicalFieldDuration (fun st=>st.2 (Sum.inl i))
      ((nativeSampledPhysicalSteps n b h as).take j)=
    physicalFieldDuration (fun st=>st.2 (Sum.inl i))
      ((sampleClockSteps (completedPathClock n b h) 0 as).take j) := by
  have H (a : ℝ) (xs : List PositiveMass) (j : ℕ) :
      physicalFieldDuration (fun st=>st.2 (Sum.inl i))
        ((sampleClockSteps (fun u=>restFiniteVariance n (nativeSampledRestClock n b h u)) a xs).take j)=
      physicalFieldDuration (fun st=>st.2 (Sum.inl i))
        ((sampleClockSteps (completedPathClock n b h) a xs).take j) := by
    induction xs generalizing a j with
    | nil => rfl
    | cons m xs ih =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [sampleClockSteps,List.take_succ_cons,physicalFieldDuration,List.map_cons,
          List.sum_cons,NNReal.coe_add]
        exact congrArg (fun z : ℝ=>((h m.val-h a : ℝ≥0):ℝ)+z) (ih m.val j)
  exact H 0 as j

theorem exists_actual_comparison_rest_boundary_projection_schedule
    (n : ℕ) (hn : 0<n) {c N d lam mesh s W ce cReg cu Rmacro F xs B : ℝ}
    {k M : ℝ→ℝ}
    (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M) (b h : ℝ→ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d) (hnd : 1/N ≤ d)
    (hlam : 0<lam) (hld : lam ≤ d^2)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hend : partitionEnd 0 as=1) (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hs : 0<s) (hsmall : mesh/c ≤ s/16) (hW : 0<W) (hWs : W ≤ s)
    (hce : 0<ce) (hstrength : ce*W^2 ≤ laplaceComparisonStrength d lam W)
    (hcReg : 0<cReg) (hcu : 0 ≤ cu) (hmacro : 0<Rmacro)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hxs : 0 ≤ xs) (hxss : xs ≤ s)
    (hregular : ∀ r∈Icc (s/2) 1,cReg*r ≤ α.val.val r ∧ α.val.val r ≤ cu*r)
    {J low high : ℕ} (hJ : 1 ≤ J) (hJmacro : Rmacro ≤ (2:ℝ)^J*s)
    (hJone : (2:ℝ)^J*s ≤ 1) (hhigh : high ≤ as.length)
    (hlow : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as low) ≤ s/2)
    (hhighradius : 2*s ≤ comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as high)) :
    let Q := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (Q u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (Q u)*Q u).toNNReal
    let steps := nativeSampledPhysicalSteps n bf hf as
    (hf 1:ℝ)-(hf 0:ℝ) ≤ B →
    ∃ (cs : List (ℝ×ℕ)) (t : ℕ) (a D : Fin cs.length→ℝ),
      cs.length=J+2 ∧ low ≤ t ∧ t ≤ high ∧ t ≤ steps.length+1 ∧
      lastLayerCut cs t=steps.length+1 ∧
      (∀ j,cutPredecessor cs t j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) ∧
      (∀ j,0<a j ∧ ce*W^3/(24*Real.log N) ≤ D j ∧ D j ≤ B ∧
        PhysicalProjectionClock n steps low (cutPredecessor cs t j) (cs.get j).2 (a j) (D j)) ∧
      (∀ i j,i ≤ j.succ → xs+physicalCutMass 0 steps (overlapComponentEnd cs t i) ≤
        (F/((cReg/8)^2*s))*(a j)^2) ∧
      ((physicalOverlapResidualPairs cs).card:ℝ)^2 ≤ ((J+3:ℕ):ℝ)^4 ∧
      0<ce*W^3/(24*Real.log N) := by
  classical
  let Q := comparisonSweepQuantile hc hk hkc hm hM α
  let rg : Fin (as.length+2)→ℝ := fun i=>Q (partitionPoint 0 as i.val)
  let τ := radiusGridCut rg
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (Q u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (Q u)*Q u).toNNReal
  let steps := nativeSampledPhysicalSteps n bf hf as
  let D₀ := ce*W^3/(24*Real.log N)
  dsimp only
  intro hBclock
  have hlogpos : 0<Real.log N := zero_lt_one.trans_le hlog
  have hmono : Monotone rg := fun i j hij=>
    comparisonSweepQuantile_monotone hc hk hkc hm hM α (partitionPoint_mono as ho hij)
  have hτ : Monotone τ := radiusGridCut_monotone rg
  have hL (r : ℝ) : τ r ≤ steps.length := by
    simpa only [steps,nativeSampledPhysicalSteps,sampleClockSteps_length] using radiusGridCut_le rg r
  have hz : rg 0=0 := by
    simpa [rg,Q,partitionPoint,partitionValues] using comparisonSweepQuantile_zero hc hk hkc hm hM α
  have hlast : rg (Fin.last (as.length+1))=1 := by
    change Q (partitionPoint 0 as (as.length+1))=1
    rw [partitionPoint_after_final 0 as _ (by omega),hend]
    exact comparisonSweepQuantile_one hc hk hkc hm hM α
  have hsteps : ∀ j : Fin (as.length+1),rg j.succ-rg j.castSucc ≤ mesh/c :=
    fun j=>actual_comparison_partition_radius_step_le hc hk hkc hm hM α as ho hmesh hpart j.val
  have htwo : 2*s ≤ (2:ℝ)^J*s := by
    have H := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hJ
    simpa only [pow_one] using mul_le_mul_of_nonneg_right H hs.le
  have hsone : s ≤ 1 := by linarith
  have had := strengthSweep_clocks_admissible b Q hd.ne' hlam.le hlb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  have hbf : MonotoneOn bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn (hh.add had.2.1)
  let fd := fun st : GaussianStep (FeatureIndex n)=>st.2 (Sum.inl ⟨0,hn⟩)
  have hB : physicalFieldDuration fd steps ≤ B := by
    have H := native_sampled_field_duration_index n bf hf hbf hhf as ho ⟨0,hn⟩ as.length le_rfl
    have he : steps.take as.length=steps := by
      have : steps.length=as.length := sampleClockSteps_length _ _ _
      rw [←this,List.take_length]
    change physicalFieldDuration fd (steps.take as.length)=_ at H
    rw [he,partitionPoint_after_final 0 as _ le_rfl,hend] at H
    rw [H]
    exact hBclock
  have hmasses (r : ℝ) (hr : r∈Icc s ((2:ℝ)^J*s)) :
      (cReg/2)*r ≤ physicalCutMass 0 steps (τ r) ∧
        physicalCutMass 0 steps (τ r) ≤ cu*r := by
    have hbnd := radiusGridPoint_bounds rg hmono (by rw [hz]; exact hs.trans_le hr.1)
      (by rw [hlast]; exact hr.2.trans hJone) hsteps
    change r-mesh/c ≤ Q (partitionPoint 0 as (τ r)) ∧
      Q (partitionPoint 0 as (τ r))<r at hbnd
    have hreg : Q (partitionPoint 0 as (τ r))∈Icc (s/2) 1 := by
      constructor
      · linarith [hbnd.1,hr.1]
      · exact (comparisonSweepQuantile_bounds hc hk hkc hm hM α _).2
    have H := hregular _ hreg
    rw [comparisonSweepQuantile_spec hc hk hkc hm hM α (partitionPoint_mem as ho (τ r))] at H
    rw [show physicalCutMass 0 steps (τ r)=partitionPoint 0 as (τ r) from
      physicalCutMass_sampleClockSteps _ _ _ _ (radiusGridCut_le rg r)]
    constructor
    · have hhalf : r/2 ≤ Q (partitionPoint 0 as (τ r)) := by linarith [hbnd.1,hr.1]
      have H' := (mul_le_mul_of_nonneg_left hhalf hcReg.le).trans H.1
      nlinarith
    · exact H.2.trans (mul_le_mul_of_nonneg_left hbnd.2.le hcu)
  have hfork : low ≤ τ s := by
    have hbnd := radiusGridPoint_bounds rg hmono (by rw [hz]; exact hs)
      (by rw [hlast]; exact hsone) hsteps
    change s-mesh/c ≤ Q (partitionPoint 0 as (τ s)) ∧ _ at hbnd
    by_contra hnot
    have H' := comparisonSweepQuantile_monotone hc hk hkc hm hM α
      (partitionPoint_mono as ho (show τ s ≤ low by omega))
    change Q (partitionPoint 0 as low) ≤ s/2 at hlow
    linarith [hbnd.1]
  have hgr (r : ℝ) (hr : r∈Icc s ((2:ℝ)^J*s)) :
      ce*W^3 ≤ laplaceComparisonStrength d lam r*r := by
    have hmgr := (laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl).2
      ⟨hW.le,hWs.trans hsone⟩ ⟨hs.le.trans hr.1,hr.2.trans hJone⟩ (hWs.trans hr.1)
    have H := mul_le_mul_of_nonneg_right hstrength hW.le
    have H' : ce*W^3 ≤ laplaceComparisonStrength d lam W*W := by nlinarith [H]
    exact H'.trans hmgr
  have hfirst : D₀ ≤ physicalFieldDuration fd (steps.take (τ (2*s)))-
      physicalFieldDuration fd (steps.take (τ s)) := by
    have H := actual_comparison_grid_field_growth n hn hc hk hkc hm hM α b h hb hlb hh hh0
      hN hlog hd hnd hlam hld as ho hmesh hpart hs
      (by linarith : s ≤ 2*s) (htwo.trans hJone)
      (by change 2*s ≤ rg (Fin.last (as.length+1)); rw [hlast]; exact htwo.trans hJone)
    have hg := hgr (2*s) ⟨by linarith,htwo⟩
    have hwidth : (2*s)/8 ≤ 2*s-s-mesh/c := by linarith
    have hgpos := laplaceComparisonStrength_pos d hlam (2*s)
    have hwid := mul_le_mul_of_nonneg_left hwidth
      (show 0 ≤ ((1:ℝ)/3)/Real.log N*laplaceComparisonStrength d lam (2*s) by positivity)
    have hsc := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1/(24*Real.log N) by positivity)
    rw [←native_sampled_field_duration_take_eq_completed n bf hf as ⟨0,hn⟩,
      ←native_sampled_field_duration_take_eq_completed n bf hf as ⟨0,hn⟩] at H
    apply le_trans _ (hwid.trans H)
    dsimp only [D₀]
    convert hsc using 1 <;> ring
  have hdyad (r : ℝ) (hr : r∈Icc (2*s) ((2:ℝ)^J*s)) :
      D₀ ≤ physicalFieldDuration fd (steps.take (τ r))-
        physicalFieldDuration fd (steps.take (τ (3*r/4))) := by
    have hrpos : 0<r := by linarith [hr.1]
    have H := actual_comparison_grid_field_growth n hn hc hk hkc hm hM α b h hb hlb hh hh0
      hN hlog hd hnd hlam hld as ho hmesh hpart (by positivity : 0<3*r/4)
      (by linarith : 3*r/4 ≤ r) (hr.2.trans hJone)
      (by change r ≤ rg (Fin.last (as.length+1)); rw [hlast]; exact hr.2.trans hJone)
    have hg := hgr r ⟨by linarith [hr.1],hr.2⟩
    have hwidth : r/8 ≤ r-3*r/4-mesh/c := by linarith [hr.1]
    have hgpos := laplaceComparisonStrength_pos d hlam r
    have hwid := mul_le_mul_of_nonneg_left hwidth
      (show 0 ≤ ((1:ℝ)/3)/Real.log N*laplaceComparisonStrength d lam r by positivity)
    have hsc := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1/(24*Real.log N) by positivity)
    rw [←native_sampled_field_duration_take_eq_completed n bf hf as ⟨0,hn⟩,
      ←native_sampled_field_duration_take_eq_completed n bf hf as ⟨0,hn⟩] at H
    apply le_trans _ (hwid.trans H)
    dsimp only [D₀]
    convert hsc using 1 <;> ring
  obtain ⟨cs,t,a,D,hlen,ht,_htlen,hlastcs,_,hends,hclock,hscale⟩ :=
    physicalOverlapDyadicCertificates n steps (sampleClockSteps_ordered _ _ ho)
      (show 0<cReg/2 by positivity) hxs hxss hs hcu hmacro hFmass hFradius hJ
      τ hτ hL hJmacro hfork fd
      (native_sampled_field_homogeneous n bf hf as ⟨0,hn⟩) hB
      (fun r hr=>(hmasses r hr).1) (fun r hr=>(hmasses r hr).2) hfirst hdyad
  have htbefore : t ≤ high := by
    rw [ht]
    have H := radiusGridPoint_bounds rg hmono (by rw [hz]; positivity : rg 0<2*s)
      (by rw [hlast]; exact htwo.trans hJone) hsteps
    change _ ∧ Q (partitionPoint 0 as (τ (2*s)))<2*s at H
    by_contra hnot
    have H' := comparisonSweepQuantile_monotone hc hk hkc hm hM α
      (partitionPoint_mono as ho (show high ≤ τ (2*s) by omega))
    change 2*s ≤ Q (partitionPoint 0 as high) at hhighradius
    linarith [H.2]
  have htlen : t ≤ steps.length+1 := by
    have H := htbefore.trans hhigh
    simpa only [steps,nativeSampledPhysicalSteps,sampleClockSteps_length] using H.trans (Nat.le_succ as.length)
  have htlow : low ≤ t := by
    rw [ht]
    exact hfork.trans (hτ (by linarith))
  refine ⟨cs,t,a,D,hlen,htlow,htbefore,htlen,hlastcs,hends,hclock,?_,?_,?_⟩
  · simpa only [show (cReg/2)/4=cReg/8 by ring] using hscale
  · have H : ((physicalOverlapResidualPairs cs).card:ℝ) ≤ ((cs.length+1:ℕ):ℝ)^2 := by
      exact_mod_cast physicalOverlapResidualPairs_card_le cs
    have H' := pow_le_pow_left₀ (Nat.cast_nonneg (physicalOverlapResidualPairs cs).card) H 2
    simpa only [hlen,Nat.add_assoc,←pow_mul] using H'
  · positivity

end OAI.SKFluctuations.Cavity
