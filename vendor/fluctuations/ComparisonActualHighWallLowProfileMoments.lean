module

public import ComparisonActualHighWallContinuumSourceMoments
public import ComparisonSignedCavityInheritedContinuumLowProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000

theorem actual_high_wall_one_pair_centered_product
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (j : ℕ) (hj : j ≤ as.length)
    (sigma : (pairClock (S:=Spin n×Bool) as j).Assignment) :
    ((nativeOnePairCenteredShape n as j).canonicalHighWallSource M (fun _=>.centered)).product sigma=
      deletedOverlap n (joinSpin (pairSpin as j sigma).1)
        (joinSpin (pairSpin as j sigma).2)-nativePhysicalResourceCenter n M.bf M.hf as j := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [Fin.prod_univ_one]
  simp only [ActualNaturalBoundaryShape.canonicalHighWallSource,
    ActualNaturalBoundaryShape.canonicalPhysicalSource,NativeSourceFactorForm.intercept,
    NativeSourceFactorForm.slope]
  rw [native_one_pair_shape_low_mass n as j hj]
  simp only [nativeOnePairCenteredShape,pairLeft_atSlot,pairRight_atSlot,fullBoundaryAffineFactor]
  change -nativePhysicalResourceCenter n M.bf M.hf as j+
    1*deletedOverlap n (joinSpin (pairSpin as j sigma).1) (joinSpin (pairSpin as j sigma).2)=_
  ring

theorem eventually_actual_high_wall_centered_low_pair_moment
    (order : ℕ) (horder : 0 < order) (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cd : ℝ,0 < Cd ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        ∀j,j ≤ as.length → partitionPoint 0 as j ≤ Ccut*M.data.d →
          (pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l t b h K)
            (fun sigma=>|deletedOverlap n (joinSpin (pairSpin as j sigma).1)
              (joinSpin (pairSpin as j sigma).2)-S j|^(2*order)) 0 ≤
            (Cd*M.data.d)^(2*order) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_canonical_continuum_square_even_moment
    (D:=D) 1 order 2 (by norm_num) horder Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cd:=Real.exp (wholeLawRowComparisonConstant 2*(2*max Bclock 0))*Cp
  refine ⟨Cd,by dsimp only [Cd];positivity,?_⟩
  filter_upwards [HP] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U l t hl ht j hj hmass
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HC:=native_ordered_source_center_eq_completed n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)
  have Hpair:=hgrid U (pairClock as j) l t hl ht (by rw [pairClock_leaves]) (nativeOnePairCenteredShape n as j)
    (fun _=>.centered) (by
      intro e
      have He : e=(0:Fin 1):=Subsingleton.elim _ _
      subst e
      rw [native_one_pair_shape_low_mass n as j hj]
      exact hmass)
  simp_rw [actual_high_wall_one_pair_centered_product M as j hj] at Hpair
  simpa only [pow_one,nativePhysicalResourceCenter,HC.symm,S,b,h,K,as,Cd,mul_assoc] using Hpair

theorem eventually_actual_high_wall_continuum_low_profile_moment
    (order : ℕ) (horder : 0 < order) (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (l t s : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 →
          partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀j,j ≤ as.length →
          (pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l t b h K)
            (fun sigma=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
              (pairSpin as j sigma).1 (pairSpin as j sigma).2|^(2*order)) 0 ≤
            (Cq*M.data.d)^(2*order) := by
  let B:=max Bclock 0
  have hB : 0 ≤ B:=le_max_right _ _
  obtain ⟨Cd,hCd,HP⟩:=eventually_actual_high_wall_centered_low_pair_moment (D:=D)
    order horder Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_high_wall_continuum_center_bound (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ck:=(1+B*Cs)*(1+Ccut)
  have hCk : 0 ≤ Ck:=by dsimp only [Ck];positivity
  refine ⟨2*(Ck+B*Cd+1),by positivity,?_⟩
  filter_upwards [HP,(tendsto_add_atTop_nat 1).eventually HS] with n hnP hnS
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U l t s hl ht hs hcut j hj
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  by_cases hju : j < U
  · have hu:=partitionPoint_mem as ho j
    have hmass : partitionPoint 0 as j ≤ Ccut*M.data.d:=(partitionPoint_mono as ho hju.le).trans hcut
    have Hsource:=M.data.small_source_clock_budget M.alpha (by rw [hwork] : M.data.d ≤ M.xs) hu
    have Hcenter:=native_ordered_source_center_eq_completed n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hu
    have HSu : |S j| ≤ Cs*(M.xs+partitionPoint 0 as j):=by
      dsimp only [S]
      rw [Hcenter]
      exact hnS M _ hu
    have Hnatural : M.xs+partitionPoint 0 as j ≤ (1+Ccut)*M.data.d:=by rw [hwork];nlinarith
    have HB : |b j| ≤ B:=by
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]
      exact Hsource.1.trans (M.hT.trans (le_max_left _ _))
    have HK : |h j+b j*S j| ≤ Ck*M.data.d:=by
      have Hprod:=mul_le_mul HB HSu (abs_nonneg _) hB
      have Hfield : |h j| ≤ M.xs+partitionPoint 0 as j:=by
        rw [abs_of_nonneg (NNReal.coe_nonneg _)]
        exact Hsource.2
      have Htri:=abs_add_le (h j) (b j*S j)
      rw [abs_mul] at Htri
      have Hscale:=mul_le_mul_of_nonneg_left Hnatural (show 0 ≤ 1+B*Cs by positivity)
      dsimp only [Ck]
      nlinarith only [Hprod,Hfield,Htri,Hscale]
    exact native_continuum_low_kernel_moment_le n U (2*order) (by omega) ho _ b h S hs j
      hCk hB hCd.le M.data.hd HK HB (hgrid U l t hl ht j hj hmass)
  · have HE : (fun sigma=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
      (pairSpin as j sigma).1 (pairSpin as j sigma).2|^(2*order))=fun _=>0:=by
      funext sigma
      simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,zero_mul,
        Finset.sum_const_zero,abs_zero,zero_pow (by omega : 2*order≠0)]
    rw [HE]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
    have hd:=M.data.hd
    positivity

end OAI.SKFluctuations.Cavity
