module

public import ComparisonSignedCavityOriginalGTargetDensity
public import ComparisonSignedCavityInheritedOriginalFreshTargetRMS
public import ComparisonSignedCavityOriginalLongitudinalConditionalReadout
public import ComparisonNativeActualUniformHighL1Density

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

def nativeActualTargetLongitudinalResponse
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let T:=single (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 (singleSlot as) i
  nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S g.tree
    (fun σ=>deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) (singleSlot as)))
      (joinSpin (g.spin σ))-S i) (g.embed (singleSlot as))

def nativeActualTargetConditionalResponse
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  nativeOriginalConditionalLongitudinalPair (single (S:=Spin n×Bool) as) (singleSlot as)
    i U K b S 0 (cutFullVariance n q U 1 1 b h K) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S i)

theorem native_actual_target_longitudinal_eq_conditional
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ)
    (hi : i<U) (hU : U≤as.length) :
    nativeActualTargetLongitudinalResponse M as i U=
      nativeActualTargetConditionalResponse M as i U := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  exact native_original_longitudinal_pair_eq_conditional_insertion
    (single (S:=Spin n×Bool) as) ho (singleSlot as) i U hi hU K b S
    0 (cutFullVariance n q U 1 1 b h K) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S i)

theorem eventually_actual_minimum_inherited_target_G_thermal_density
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf→M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i U : ℕ),i<U→U≤as.length→
        ∀x : ℝ,M.xs ≤ x→partitionPoint 0 as i ≤ Ccut*x→
          let tail:=(∫u in partitionPoint 0 as U..1,
            Real.sqrt (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))+
              3/(n+1:ℕ)
          abs (nativeActualTargetLongitudinalResponse M as i U) ≤ C*x*tail ∧
          abs (nativeActualTargetConditionalResponse M as i U) ≤ C*x*tail := by
  obtain ⟨Cr,hCr,Hr⟩:=eventually_actual_minimum_inherited_original_fresh_target_rms
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let V:=forkVariation 2 3
  let Cmp:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  have hV : 0≤V:=forkVariation_nonneg 2 3
  have hCmp : 0≤Cmp:=actualLowErrorComparisonConstant_nonneg _ hTemp
  refine ⟨Cr*V*Cmp+1,by positivity,?_⟩
  filter_upwards [Hr] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh,
    M.actual_original_high_l1_density_on_all_final_nets] with jGrid hj htail
  dsimp only at hj ⊢
  intro i U hi hU x hscale hmass
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hx : 0≤x:=M.hxs.le.trans hscale
  have HR:=hj U 1 1 (by norm_num) (by norm_num)
    (single (S:=Spin n×Bool) (finiteCutMasses us jGrid))
    (singleSlot (finiteCutMasses us jGrid)) i (Nat.le_trans hi.le hU) x hscale hmass
  have HP:=(Real.sqrt_le_iff.mp HR).2
  let T:=single (S:=Spin n×Bool) (finiteCutMasses us jGrid)
  let g:=nativeFreshAtSlot T 0 (singleSlot (finiteCutMasses us jGrid)) i
  let P:=fun σ=>deletedOverlap n
    (joinSpin (T.atSlot (g.restrict σ) (singleSlot (finiteCutMasses us jGrid))))
    (joinSpin (g.spin σ))-orderedPathS (n+1) M.bf M.hf
      (partitionPoint 0 (finiteCutMasses us jGrid) i)
  have HL:=actual_minimum_inherited_original_target_G_density M Temp Cf hTemp hCf
    hsource hxs (finiteCutMasses us jGrid) ho i U hi hU (Cr*x) (mul_nonneg hCr.le hx) P HP
  have HE:=htail us hus U hU
  let edge:=edgeBudget 0 (finiteCutMasses us jGrid)
    (fun j=>if j<U then 0 else nativeOriginalCutLowErrorRadius n M.bf M.hf
      (finiteCutMasses us jGrid) j+1/(n+1:ℕ))
  have he : 0≤edge:=edgeBudget_nonneg ho (by
    intro j
    split_ifs
    · exact le_rfl
    · exact add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have HT : (0:ℝ)≤_:=he.trans HE
  change abs (nativeActualTargetLongitudinalResponse M (finiteCutMasses us jGrid) i U)≤
    (Cr*x)*V*Cmp*edge at HL
  have Hbound:=HL.trans (mul_le_mul_of_nonneg_left HE
    (mul_nonneg (mul_nonneg (mul_nonneg hCr.le hx) hV) hCmp))
  have Hfinal : abs (nativeActualTargetLongitudinalResponse M (finiteCutMasses us jGrid) i U)≤
      (Cr*V*Cmp+1)*x*((∫u in partitionPoint 0 (finiteCutMasses us jGrid) U..1,
        Real.sqrt (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))+3/(n+1:ℕ)) := by
    have Hcoef : (Cr*x)*V*Cmp=(Cr*V*Cmp)*x:=by ring
    rw [Hcoef] at Hbound
    exact Hbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hx) HT)
  refine ⟨Hfinal,?_⟩
  rwa [←native_actual_target_longitudinal_eq_conditional M _ ho i U hi hU]

end OAI.SKFluctuations.Cavity
