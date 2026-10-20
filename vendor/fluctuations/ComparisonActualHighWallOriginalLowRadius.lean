module

public import ComparisonActualHighWallSourceMoments
public import ComparisonSignedCavityActualLowErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

theorem actual_finite_weighted_centered_square_le
    {A : Type*} [Fintype A] (p F : A→ℝ) (c : ℝ)
    (hp : ∀a,0 ≤ p a) (hmass : ∑a,p a=1) :
    (∑a,p a*(F a-c)^2) ≤ 2*(∑a,p a*(F a)^2)+2*c^2 := by
  have H:=Finset.sum_le_sum (fun a (_ : a∈Finset.univ)=>
    mul_le_mul_of_nonneg_left (show (F a-c)^2 ≤ 2*(F a)^2+2*c^2 by
      nlinarith [sq_nonneg (F a+c)]) (hp a))
  have HE : (∑a,p a*(2*(F a)^2+2*c^2))=
      2*(∑a,p a*(F a)^2)+2*c^2 := by
    simp only [mul_add,Finset.sum_add_distrib]
    rw [show (∑a,p a*(2*c^2))=(2*c^2)*(∑a,p a) by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a _;ring,hmass,mul_one]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  exact H.trans_eq HE

theorem actual_clock_centered_square_le_raw
    {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
    {as : List PositiveMass} (V : ClockTree S as)
    {w : S→ℝ} (hw : ∀s,0 < w s) (phi : S→(I→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v : I→ℝ) (q : ℕ→I→ℝ) (x : I→ℝ)
    (F : V.Assignment→ℝ) (c : ℝ) :
    V.disorderExpect w phi v q (fun sigma=>(F sigma-c)^2) x ≤
      2*V.disorderExpect w phi v q (fun sigma=>(F sigma)^2) x+2*c^2 := by
  exact actual_finite_weighted_centered_square_le _ F c
    (V.disorderWeight_probability hw phi ho v q x).1
    (V.disorderWeight_probability hw phi ho v q x).2

theorem eventually_actual_high_wall_original_low_error_radius_bigO
    (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀j,j≤as.length → partitionPoint 0 as j ≤ Ccut*M.data.d →
          nativeOriginalCutLowErrorRadius n M.bf M.hf as j ≤ C*M.data.d := by
  obtain ⟨K,hK,Hraw⟩:=eventually_actual_high_wall_finite_overlap_on_retained_net
    (D:=D) 0 Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,Hcenter⟩:=eventually_actual_high_wall_continuum_center_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=(2*K+2*Cs^2+1)*(1+Ccut)
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hraw,
    (tendsto_add_atTop_nat 1).eventually Hcenter] with n hnRaw hnCenter
  intro M hwork L us hus hret hmesh
  filter_upwards [hnRaw M L us hus hret hmesh] with jGrid hjRaw
  dsimp only at hjRaw ⊢
  intro j hj hmass
  let as:=finiteCutMasses us jGrid
  let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
  let q:=physicalCompletedClock (n+1) b h
  let S:=orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let natScale:=M.xs+partitionPoint 0 as j
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hb:=M.data.bf_monotone M.alpha
  have hh:=M.data.hf_monotone M.alpha
  have hdiag:=actual_sampled_completed_diagonal_steps_eq (n+1) M.bf M.hf hb hh as ho
  have hq:=actual_sampled_completed_clock_eq (n+1) M.bf M.hf hb hh as ho
  have hz (i : FeatureIndex (n+1)) : q 0 i=(completedPathClock (n+1) M.bf M.hf 0 i:ℝ) := by
    have H:=congrFun (congrFun hq.symm 0) i
    simpa only [stepClockValues_zero] using H
  have hroot : (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))=
      Measure.pi fun i=>gaussianReal 0 (completedPathClock (n+1) M.bf M.hf 0 i) := by
    congr 1
    funext i
    rw [hz,Real.toNNReal_coe]
  have Hraw' : physicalOverlapMoment (n+1) 1
      (diagonalBoundarySteps as (q 0) (fun k=>q (k+1)))
      (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i))) id measurable_id j ≤ K*natScale^2 := by
    rw [hdiag,hroot]
    simpa only [Nat.zero_add,Nat.mul_one,physicalCutMass_sampleClockSteps _ _ _ j hj,natScale,as]
      using hjRaw j hj
  rw [physicalOverlapMoment_eq_actual_pair (n+1) 1 as ho q j hj] at Hraw'
  simp only [Nat.mul_one,sq_abs] at Hraw'
  have Hcenter' : |S|≤Cs*natScale:=by
    have H:=hnCenter M _ (partitionPoint_mem as ho j)
    dsimp only [S,natScale]
    rw [native_ordered_source_center_eq_completed n M.bf M.hf hb hh (partitionPoint_mem as ho j)]
    exact H
  have Hc2 : S^2 ≤ Cs^2*natScale^2:=by
    have H:=pow_le_pow_left₀ (abs_nonneg S) Hcenter' 2
    simpa only [sq_abs,mul_pow] using H
  have Hsecond:=actual_clock_centered_square_le_raw (pairClock (S:=Spin (n+1)) as j)
    (uniformWeight_pos (n+1)) (finiteFeature (n+1)) ho 0 q 0
    (fun sigma=>orderedOverlap (n+1) (pairSpin as j sigma).1 (pairSpin as j sigma).2) S
  have Horig : nativeOriginalCutLowErrorSecond n M.bf M.hf as j ≤
      (2*K+2*Cs^2)*natScale^2 := by
    rw [nativeOriginalCutLowErrorSecond_eq_pairDisorder n M.bf M.hf hb hh ho]
    change _ ≤ _ at Hsecond
    nlinarith only [Hsecond,Hraw',Hc2]
  have hnat : 0 ≤ natScale:=add_nonneg M.hxs.le (partitionPoint_mem as ho j).1
  have Hnat : natScale ≤ (1+Ccut)*M.data.d:=by dsimp only [natScale];rw [hwork];nlinarith only [hmass]
  have Hp:=pow_le_pow_left₀ hnat Hnat 2
  have HC : 2*K+2*Cs^2 ≤ (2*K+2*Cs^2+1)^2 := by nlinarith [sq_nonneg (2*K+2*Cs^2)]
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hC.le M.data.hd.le,?_⟩
  have H1:=mul_le_mul_of_nonneg_left Hp (show 0 ≤ 2*K+2*Cs^2 by positivity)
  have H2:=mul_le_mul_of_nonneg_right HC (sq_nonneg ((1+Ccut)*M.data.d))
  apply Horig.trans (H1.trans (H2.trans_eq ?_))
  dsimp only [C]
  ring

end OAI.SKFluctuations.Cavity
