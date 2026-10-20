module

public import ComparisonSignedCavityOriginalGPairLawAdapter
public import ComparisonSignedCavityActualGProjectedRowLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem native_decoupled_G_projected_displacement_eq_retained
    (n : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j) (hU : U ≤ as.length)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) :
    nativeActualOriginalGProjectedDisplacement T s star U K b C 0
      (cutFullVariance n q U 0 0 b h K) 0 (fun σ τ=>A σ.1 τ.1)
      (fun σ=>P (T.cavityAssignment σ).1)=
      nativeRetainedGProjectedDisplacement T s star U q b h K A P := by
  unfold nativeActualOriginalGProjectedDisplacement nativeRetainedGProjectedDisplacement
  dsimp only
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  have Htest : (fun σ : p.tree.Assignment=>
      (A (p.spin σ).1 ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ)).1-
        A (T.atSlot ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ)) s).1
          ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ)).1)*
        P (T.cavityAssignment ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ))).1)=
      (fun σ=>nativeRestProjectedDisplacementTest T s star A P p (p.tree.cavityAssignment σ).1) := by
    funext σ
    exact (native_rest_projected_displacement_test_actual T s star A P p σ).symm
  rw [Htest]
  exact native_decoupled_connected_response_eq_retained n q U b h K C hKC p.tree ho
    (nativeRestProjectedDisplacementTest T s star A P p) (p.embed ((nativeFreshAtSlot T 0 s star).embed s))
    p.mark hU

theorem native_generated_G_projected_resampling_law_restoration
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star<U)
    (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ) (hKC : ∀j,K j=h j+b j*C j)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeActualOriginalGProjectedResampling T P₀.live.test.target star U K b C 0
      (cutFullVariance n q U 1 1 b h K) 0 (fun σ τ=>A σ.1 τ.1)
      (fun σ=>P (T.cavityAssignment σ).1)=
      nativeActualOriginalGProjectedResampling T P₀.live.test.target star U K b C 0
        (cutFullVariance n q U 0 0 b h K) 0 (fun σ τ=>A σ.1 τ.1)
        (fun σ=>P (T.cavityAssignment σ).1)+
      2*nativeOriginalGProjectedDisplacementRestoration T P₀.live.test.target star U q b h K C A P := by
  have Hfull:=native_actual_original_G_pair_half_eq_rest_add_restoration hP hi hs ho q b h K C
    hKC A P hq0 hq hb hh hK hbm hhm hKm
  have hfull : ∀i,Monotone (fun j=>cutFullVariance n q U 0 0 b h K j i) :=
    cutFullVariance_monotone n q U (by norm_num) (by norm_num) hq hb hh hK hbm hhm hKm
  have hzero : ∀i,(0 : FullCoordinate n→ℝ) i ≤ cutFullVariance n q U 0 0 b h K 0 i :=
    fun i=>cutFullVariance_nonneg n q U (by norm_num) (by norm_num) hq0 hb hh hK 0 i
  have Hzero:=native_actual_generated_original_G_projected_row_polarization hP hi hs ho 0
    (cutFullVariance n q U 0 0 b h K) 0 K b C hfull hzero hK hKm
    (fun σ τ=>A σ.1 τ.1) (fun σ=>P (T.cavityAssignment σ).1)
  rw [native_decoupled_G_projected_displacement_eq_retained n T ho P₀.live.test.target star U q b h K C
    hKC hP.highCut_le_length A P] at Hzero
  linear_combination 2*Hfull+2*Hzero

def nativeActualCoupledGProjectedResampling
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : NativeGeneratedTest T) (star U : ℕ)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (q : ℕ→RestCoordinate n→ℝ) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  nativeActualOriginalGProjectedResampling T P.target star U K b C 0
    (cutFullVariance n q U 1 1 b h K) 0 (fun u v=>R u.1 v.1)
    (P.value (fun u v=>R u.1 v.1) C)

def nativeActualGProjectedRestoration
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : NativeGeneratedTest T) (star U : ℕ)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (q : ℕ→RestCoordinate n→ℝ) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  nativeOriginalGProjectedDisplacementRestoration T P.target star U q b h K C R
    (nativeRestGeneratedTestValue T P R C)

theorem native_actual_current_G_coupled_eq_decoupled_add_restoration
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star) (hs : star<U)
    (ho : MassOrdered 0 as)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock) :
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
      (fun _=>((M.bf (partitionPoint 0 as j)):ℝ)) (fun _=>((M.hf (partitionPoint 0 as j)):ℝ))
    nativeActualCoupledGProjectedResampling T P.live.test star U M q=
      nativeActualDecoupledGProjectedResampling T P.live.test star U M q+
      2*nativeActualGProjectedRestoration T P.live.test star U M q := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HC j : S j=C j:=native_ordered_source_center_eq_completed n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have H:=native_generated_G_projected_resampling_law_restoration hP hi hs ho q b h K C
    (fun j=>by dsimp only [K];rw [HC]) R (nativeRestGeneratedTestValue T P.live.test R C)
    (fun j v=>by cases v <;> exact NNReal.coe_nonneg _)
    (fun v=>by cases v <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
  simp only [native_rest_generated_value_eq_full] at H
  exact H

end OAI.SKFluctuations.Cavity
