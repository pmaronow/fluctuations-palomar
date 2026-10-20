module

public import ComparisonActualGeneralInitialLowMomentInterpolation
public import ComparisonSignedCavityActualLowErrorTransport

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

def originalInitialPairComparisonConstant (Mclock Temp : ℝ) : ℝ :=
  Real.sqrt (2*Real.exp (220*Mclock)*(Real.exp (110*Temp)+1))

theorem original_initial_pair_comparison_constant_pos (Mclock Temp : ℝ) :
    0<originalInitialPairComparisonConstant Mclock Temp := by
  unfold originalInitialPairComparisonConstant
  apply Real.sqrt_pos.mpr
  positivity

theorem actual_original_initial_pair_second_transport (n U : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} (ho : MassOrdered 0 as) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    {Mclock Temp : ℝ}
    (hbond : ∀j,j ≤ as.length → (bf (partitionPoint 0 as j):ℝ) ≤ Temp)
    (hclock : (hf (partitionPoint 0 as as.length):ℝ)+
      (bf (partitionPoint 0 as as.length):ℝ)*orderedPathS (n+1) bf hf (partitionPoint 0 as as.length)+
      (bf (partitionPoint 0 as as.length):ℝ)+(hf (partitionPoint 0 as as.length):ℝ) ≤ Mclock)
    (j : ℕ) (hj : j ≤ as.length) :
    let b:=fun k=>(bf (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(hf (partitionPoint 0 as k):ℝ)
    let S:=fun k=>orderedPathS (n+1) bf hf (partitionPoint 0 as k)
    let K:=fun k=>h k+b k*S k
    (Hierarchy.ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n (fun k=>Sum.elim (fun _=>b k) (fun _=>h k)) U l t b h K)
      (fun σ=>|deletedOverlap n (joinSpin (Hierarchy.ClockTree.pairSpin as j σ).1)
        (joinSpin (Hierarchy.ClockTree.pairSpin as j σ).2)-S j|^2) 0 ≤ 
      (originalInitialPairComparisonConstant Mclock Temp*
        (nativeOriginalCutLowErrorRadius n bf hf as j+1/(n+1:ℕ)))^2 := by
  dsimp only
  let b:=fun k=>(bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>(hf (partitionPoint 0 as k):ℝ)
  let S:=fun k=>orderedPathS (n+1) bf hf (partitionPoint 0 as k)
  let K:=fun k=>h k+b k*S k
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (bf u:ℝ) ≤ bf v from hb hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (hf u:ℝ) ≤ hf v from hh hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone (physicalOrderedPathS_monotone_unit n bf hf hb hh) as ho
  have hS0 k : 0 ≤ S k:=(physicalOrderedPathS_mem_unit n bf hf hb hh (partitionPoint_mem as ho k)).1
  have hK0 k : 0 ≤ K k:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (hS0 k))
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (hS0 i) (NNReal.coe_nonneg _))
  have H:=cavityPath_pairDeleted_moment_le_physicalStar n 1 U ho hl ht hbm hhm hKm
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 j hj (S j)
  dsimp only at H
  rw [nativeOriginalCutLowErrorSecond_eq_physicalStar n bf hf hb hh ho j hj] at H
  simp only [Nat.mul_one,show 2-1=1 by omega,pow_one] at H
  let R:=nativeOriginalCutLowErrorRadius n bf hf as j
  let site:=(1/(n+1:ℕ):ℝ)
  have hR : 0 ≤ R:=Real.sqrt_nonneg _
  have hsite : 0 ≤ site:=by dsimp [site];positivity
  have HR : nativeOriginalCutLowErrorSecond n bf hf as j=R^2:=
    (Real.sq_sqrt (nativeOriginalCutLowErrorSecond_nonneg n bf hf ho j)).symm
  have Hclock : Real.exp (220*(K as.length+b as.length+h as.length)) ≤ Real.exp (220*Mclock):=
    Real.exp_le_exp.mpr (by dsimp [K,b,h];linarith)
  have Hbond : Real.exp (110*b as.length) ≤ Real.exp (110*Temp):=
    Real.exp_le_exp.mpr (by have HH:=hbond as.length le_rfl;dsimp [b];linarith)
  have Hfirst : (Hierarchy.ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n (fun k=>Sum.elim (fun _=>b k) (fun _=>h k)) U l t b h K)
      (fun σ=>|deletedOverlap n (joinSpin (Hierarchy.ClockTree.pairSpin as j σ).1)
        (joinSpin (Hierarchy.ClockTree.pairSpin as j σ).2)-S j|^2) 0 ≤ 
      Real.exp (220*Mclock)*2*(Real.exp (110*Temp)*R^2+site^2) := by
    apply H.trans
    rw [HR]
    gcongr
  have Hraw : Real.exp (110*Temp)*R^2+site^2 ≤ (Real.exp (110*Temp)+1)*(R+site)^2:=by
    have H1:=mul_nonneg (Real.exp_pos (110*Temp)).le (sq_nonneg site)
    have H2:=mul_nonneg (Real.exp_pos (110*Temp)).le (mul_nonneg hR hsite)
    nlinarith [sq_nonneg R,mul_nonneg hR hsite]
  have Hfinal:=Hfirst.trans (mul_le_mul_of_nonneg_left Hraw (by positivity : 0 ≤ Real.exp (220*Mclock)*2))
  convert Hfinal using 1
  rw [mul_pow,originalInitialPairComparisonConstant,
      Real.sq_sqrt (by positivity : 0 ≤ 2*Real.exp (220*Mclock)*(Real.exp (110*Temp)+1))]
  dsimp only [R,site]
  ring

end OAI.SKFluctuations.Cavity
