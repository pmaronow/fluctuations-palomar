module

public import ComparisonActualHighWallInnovation
public import ComparisonActualGeneralSampledFieldTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal RealInnerProductSpace
set_option maxHeartbeats 10000000

theorem exists_actual_high_wall_rest_boundary_projection_schedule
    {N : ℕ} {delta : ℝ} (w : ActualHighWallData N delta) (alpha : w.Profile)
    (n : ℕ) (hn : 0 < n)
    {mesh s W ce cReg cu Rmacro F xs : ℝ}
    (hN : 1 ≤ w.N) (hlog : 1 ≤ Real.log w.N) (hnd : 1/w.N ≤ w.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hend : partitionEnd 0 as=1) (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hs : 0 < s) (hwall : w.rmin ≤ s/2) (hsmall : mesh/(w.k 1) ≤ s/16)
    (hW : 0 < W) (hWs : W ≤ s)
    (hce : 0 < ce) (hstrength : ce*W^2 ≤ w.g W)
    (hcReg : 0 < cReg) (hcu : 0 ≤ cu) (hmacro : 0 < Rmacro)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hxs : 0 ≤ xs) (hxss : xs ≤ s)
    (hregular : ∀ r ∈ Icc (s/2) 1,cReg*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r)
    {J low high : ℕ} (hJ : 1 ≤ J) (hJmacro : Rmacro ≤ (2:ℝ)^J*s)
    (hJone : (2:ℝ)^J*s ≤ 1) (hhigh : high ≤ as.length)
    (hlow : w.wallRadius alpha (partitionPoint 0 as low) ≤ s/2)
    (hhighradius : 2*s ≤ w.wallRadius alpha (partitionPoint 0 as high)) :
    let steps := nativeSampledPhysicalSteps n (w.bf alpha) (w.hf alpha) as
    ∃ (cs : List (ℝ×ℕ)) (t : ℕ) (a D : Fin cs.length→ℝ),
      cs.length=J+2 ∧ low ≤ t ∧ t ≤ high ∧ t ≤ steps.length+1 ∧
      lastLayerCut cs t=steps.length+1 ∧
      (∀ j,cutPredecessor cs t j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) ∧
      (∀ j,0<a j ∧ ce*W^3/(24*Real.log w.N) ≤ D j ∧ D j ≤ w.T ∧
        PhysicalProjectionClock n steps low (cutPredecessor cs t j) (cs.get j).2 (a j) (D j)) ∧
      (∀ i j,i ≤ j.succ → xs+physicalCutMass 0 steps (overlapComponentEnd cs t i) ≤
        (F/((cReg/8)^2*s))*(a j)^2) ∧
      ((physicalOverlapResidualPairs cs).card:ℝ)^2 ≤ ((J+3:ℕ):ℝ)^4 ∧
      0<ce*W^3/(24*Real.log w.N) := by
  classical
  let Q := w.wallRadius alpha
  let rg : Fin (as.length+2)→ℝ := fun i=>Q (partitionPoint 0 as i.val)
  let τ := radiusGridCut rg
  let bf := w.bf alpha
  let hf := w.hf alpha
  let steps := nativeSampledPhysicalSteps n bf hf as
  let D₀ := ce*W^3/(24*Real.log w.N)
  dsimp only
  have hBclock := w.field_clock_budget alpha
  have hlogpos : 0<Real.log w.N := zero_lt_one.trans_le hlog
  have hmono : Monotone rg := fun i j hij=>
    w.wallRadius_monotone alpha (partitionPoint_mono as ho hij)
  have hτ : Monotone τ := radiusGridCut_monotone rg
  have hL (r : ℝ) : τ r ≤ steps.length := by
    simpa only [steps,nativeSampledPhysicalSteps,sampleClockSteps_length] using radiusGridCut_le rg r
  have hz : rg 0=w.rmin := by
    simpa [rg,Q,partitionPoint]
      using w.wallRadius_before alpha (u:=0) w.hs.1.le
  have hlast : rg (Fin.last (as.length+1))=1 := by
    change Q (partitionPoint 0 as (as.length+1))=1
    rw [partitionPoint_after_final 0 as _ (by omega),hend]
    exact w.wallRadius_one alpha
  have hsteps : ∀ j : Fin (as.length+1),rg j.succ-rg j.castSucc ≤ mesh/(w.k 1) :=
    fun j=>w.sampled_radius_step_le alpha as ho hmesh hpart j.val
  have htwo : 2*s ≤ (2:ℝ)^J*s := by
    have H := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hJ
    simpa only [pow_one] using mul_le_mul_of_nonneg_right H hs.le
  have hsone : s ≤ 1 := by linarith
  have hbf : MonotoneOn bf (Icc (0:ℝ) 1) := w.bf_monotone alpha
  have hhf : MonotoneOn hf (Icc (0:ℝ) 1) := w.hf_monotone alpha
  let fd := fun st : GaussianStep (FeatureIndex n)=>st.2 (Sum.inl ⟨0,hn⟩)
  have hB : physicalFieldDuration fd steps ≤ w.T := by
    have H := sampledFieldDuration_index n hn bf hf hbf hhf as ho as.length le_rfl
    have he : steps.take as.length=steps := by
      have : steps.length=as.length := by simp only [steps,nativeSampledPhysicalSteps,sampleClockSteps_length]
      rw [←this,List.take_length]
    dsimp only at H
    rw [physicalCutMass_sampleClockSteps _ _ _ _ le_rfl] at H
    rw [←native_sampled_field_duration_take_eq_completed n bf hf as ⟨0,hn⟩] at H
    change physicalFieldDuration fd (steps.take as.length)=_ at H
    rw [he,partitionPoint_after_final 0 as _ le_rfl,hend] at H
    rw [H]
    exact hBclock
  have hmasses (r : ℝ) (hr : r∈Icc s ((2:ℝ)^J*s)) :
      (cReg/2)*r ≤ physicalCutMass 0 steps (τ r) ∧
        physicalCutMass 0 steps (τ r) ≤ cu*r := by
    have hbnd := radiusGridPoint_bounds rg hmono (by rw [hz]; linarith [hr.1] : rg 0 < r)
      (by rw [hlast]; exact hr.2.trans hJone) hsteps
    change r-mesh/(w.k 1) ≤ Q (partitionPoint 0 as (τ r)) ∧
      Q (partitionPoint 0 as (τ r))<r at hbnd
    have hreg : Q (partitionPoint 0 as (τ r))∈Icc (s/2) 1 := by
      constructor
      · linarith [hbnd.1,hr.1]
      · exact (w.wallRadius_bounds alpha _).2
    have H := hregular _ hreg
    have hradabove : w.rmin < w.wallRadius alpha (partitionPoint 0 as (τ r)) := by
      change w.rmin < Q (partitionPoint 0 as (τ r))
      linarith [hbnd.1,hr.1]
    have hmasshigh : w.s ≤ partitionPoint 0 as (τ r) :=
      (w.wallRadius_high_mass alpha hradabove).le
    rw [w.wallRadius_spec alpha ⟨hmasshigh,(partitionPoint_mem as ho (τ r)).2⟩] at H
    rw [show physicalCutMass 0 steps (τ r)=partitionPoint 0 as (τ r) from
      physicalCutMass_sampleClockSteps _ _ _ _ (radiusGridCut_le rg r)]
    constructor
    · have hhalf : r/2 ≤ Q (partitionPoint 0 as (τ r)) := by linarith [hbnd.1,hr.1]
      have H' := (mul_le_mul_of_nonneg_left hhalf hcReg.le).trans H.1
      nlinarith
    · exact H.2.trans (mul_le_mul_of_nonneg_left hbnd.2.le hcu)
  have hfork : low ≤ τ s := by
    have hbnd := radiusGridPoint_bounds rg hmono (by rw [hz]; linarith : rg 0 < s)
      (by rw [hlast]; exact hsone) hsteps
    change s-mesh/(w.k 1) ≤ Q (partitionPoint 0 as (τ s)) ∧ _ at hbnd
    by_contra hnot
    have H' := w.wallRadius_monotone alpha
      (partitionPoint_mono as ho (show τ s ≤ low by omega))
    change Q (partitionPoint 0 as low) ≤ s/2 at hlow
    linarith [hbnd.1]
  have hgr (r : ℝ) (hr : r∈Icc s ((2:ℝ)^J*s)) :
      ce*W^3 ≤ w.g r*r := by
    have hmgr := (laplaceComparisonStrength_monotonicities w.hd.ne' (sq_pos_of_pos w.hd) (r₀:=0) le_rfl).2
      ⟨hW.le,hWs.trans hsone⟩ ⟨hs.le.trans hr.1,hr.2.trans hJone⟩ (hWs.trans hr.1)
    have H := mul_le_mul_of_nonneg_right hstrength hW.le
    have H' : ce*W^3 ≤ w.g W*W := by nlinarith [H]
    exact H'.trans hmgr
  have hfirst : D₀ ≤ physicalFieldDuration fd (steps.take (τ (2*s)))-
      physicalFieldDuration fd (steps.take (τ s)) := by
    have H := w.sampled_grid_field_growth alpha hN hlog hnd as ho hmesh hpart
      (by linarith : w.rmin < s-mesh/(w.k 1))
      (by linarith : s ≤ 2*s) (htwo.trans hJone)
      (by change 2*s ≤ rg (Fin.last (as.length+1)); rw [hlast]; exact htwo.trans hJone)
    rw [←actual_general_sampled_field_duration_dimension_transport n N hn w.hn bf hf hbf hhf as ho (τ (2*s)) (radiusGridCut_le rg _),
      ←actual_general_sampled_field_duration_dimension_transport n N hn w.hn bf hf hbf hhf as ho (τ s) (radiusGridCut_le rg _)] at H
    have hg := hgr (2*s) ⟨by linarith,htwo⟩
    have hwidth : (2*s)/8 ≤ 2*s-s-mesh/(w.k 1) := by linarith
    have hgpos := laplaceComparisonStrength_pos w.d (sq_pos_of_pos w.hd) (2*s)
    have hwid := mul_le_mul_of_nonneg_left hwidth
      (show 0 ≤ ((1:ℝ)/3)/Real.log w.N*w.g (2*s) by positivity)
    have hsc := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1/(24*Real.log w.N) by positivity)
    apply le_trans _ (hwid.trans H)
    dsimp only [D₀]
    convert hsc using 1 <;> ring
  have hdyad (r : ℝ) (hr : r∈Icc (2*s) ((2:ℝ)^J*s)) :
      D₀ ≤ physicalFieldDuration fd (steps.take (τ r))-
        physicalFieldDuration fd (steps.take (τ (3*r/4))) := by
    have hrpos : 0<r := by linarith [hr.1]
    have H := w.sampled_grid_field_growth alpha hN hlog hnd as ho hmesh hpart
      (by linarith [hr.1] : w.rmin < 3*r/4-mesh/(w.k 1))
      (by linarith : 3*r/4 ≤ r) (hr.2.trans hJone)
      (by change r ≤ rg (Fin.last (as.length+1)); rw [hlast]; exact hr.2.trans hJone)
    rw [←actual_general_sampled_field_duration_dimension_transport n N hn w.hn bf hf hbf hhf as ho (τ r) (radiusGridCut_le rg _),
      ←actual_general_sampled_field_duration_dimension_transport n N hn w.hn bf hf hbf hhf as ho (τ (3*r/4)) (radiusGridCut_le rg _)] at H
    have hg := hgr r ⟨by linarith [hr.1],hr.2⟩
    have hwidth : r/8 ≤ r-3*r/4-mesh/(w.k 1) := by linarith [hr.1]
    have hgpos := laplaceComparisonStrength_pos w.d (sq_pos_of_pos w.hd) r
    have hwid := mul_le_mul_of_nonneg_left hwidth
      (show 0 ≤ ((1:ℝ)/3)/Real.log w.N*w.g r by positivity)
    have hsc := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1/(24*Real.log w.N) by positivity)
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
    have H := radiusGridPoint_bounds rg hmono (by rw [hz]; linarith : rg 0<2*s)
      (by rw [hlast]; exact htwo.trans hJone) hsteps
    change _ ∧ Q (partitionPoint 0 as (τ (2*s)))<2*s at H
    by_contra hnot
    have H' := w.wallRadius_monotone alpha
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
