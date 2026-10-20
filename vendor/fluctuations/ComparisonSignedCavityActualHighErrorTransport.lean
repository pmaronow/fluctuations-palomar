module

public import ComparisonSignedCavityActualLowErrorTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem native_actual_high_error_radius_le_original (n U : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} (ho : MassOrdered 0 as) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    {M Temp : ℝ} (hTemp : 0 ≤ Temp)
    (hbond : ∀j,j ≤ as.length → (bf (partitionPoint 0 as j):ℝ) ≤ Temp)
    (hclock : (hf (partitionPoint 0 as as.length):ℝ)+
      (bf (partitionPoint 0 as as.length):ℝ)*orderedPathS (n+1) bf hf (partitionPoint 0 as as.length)+
      (bf (partitionPoint 0 as as.length):ℝ)+(hf (partitionPoint 0 as as.length):ℝ) ≤ M)
    (j : ℕ) (hj : j ≤ as.length) :
    let b:=fun k=>(bf (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(hf (partitionPoint 0 as k):ℝ)
    let S:=fun k=>orderedPathS (n+1) bf hf (partitionPoint 0 as k)
    let K:=fun k=>h k+b k*S k
    nativeWholeLawErrorRadius n as
      (cutFullVariance n (fun k=>Sum.elim (fun _=>b k) (fun _=>h k)) U l t b h K)
      (cutTSlope n U 0 b h K) j ≤
      if j<U then 0 else actualLowErrorComparisonConstant M Temp*
        (nativeOriginalCutLowErrorRadius n bf hf as j+1/(n+1:ℕ)) := by
  dsimp only
  let b:=fun k=>(bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>(hf (partitionPoint 0 as k):ℝ)
  let S:=fun k=>orderedPathS (n+1) bf hf (partitionPoint 0 as k)
  let K:=fun k=>h k+b k*S k
  let q:=cutFullVariance n (fun k=>Sum.elim (fun _=>b k) (fun _=>h k)) U l t b h K
  let A:=cutTSlope n U 0 b h K
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
  by_cases hhigh : ¬j<U
  · rw [ite_eq_right hhigh]
    have H:=nativeWholeLaw_high_error_pair_second_le_star n U ho hl ht b h S hbm hhm hKm
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 j hj
    dsimp only at H
    rw [nativeOriginalCutLowErrorSecond_eq_physicalStar n bf hf hb hh ho j hj] at H
    let R:=nativeOriginalCutLowErrorRadius n bf hf as j
    let site:=(1/(n+1:ℕ):ℝ)
    have hR : 0 ≤ R:=Real.sqrt_nonneg _
    have hsite : 0 ≤ site:=by dsimp [site];positivity
    have HR : nativeOriginalCutLowErrorSecond n bf hf as j=R^2:=
      (Real.sq_sqrt (nativeOriginalCutLowErrorSecond_nonneg n bf hf ho j)).symm
    have Hb : b j^2 ≤ Temp^2:=pow_le_pow_left₀ (NNReal.coe_nonneg _) (hbond j hj) 2
    have Hclock : Real.exp (220*(K as.length+b as.length+h as.length)) ≤ Real.exp (220*M):=
      Real.exp_le_exp.mpr (by dsimp [K,b,h];linarith)
    have Hbond : Real.exp (110*b as.length) ≤ Real.exp (110*Temp):=
      Real.exp_le_exp.mpr (by have HH:=hbond as.length le_rfl; dsimp [b];linarith)
    have Hfirst : nativeWholeLawErrorSecond n as q A j ≤
        Temp^2*Real.exp (220*M)*2*(Real.exp (110*Temp)*R^2+site^2) := by
      apply H.trans
      rw [HR]
      gcongr
    have Hraw : Real.exp (110*Temp)*R^2+site^2 ≤
        (Real.exp (110*Temp)+1)*(R+site)^2 := by
      have H1:=mul_nonneg (Real.exp_pos (110*Temp)).le (sq_nonneg site)
      have H2:=mul_nonneg (Real.exp_pos (110*Temp)).le (mul_nonneg hR hsite)
      nlinarith [sq_nonneg R,mul_nonneg hR hsite]
    have Hfinal := Hfirst.trans (mul_le_mul_of_nonneg_left Hraw
      (show 0 ≤ Temp^2*Real.exp (220*M)*2 by positivity))
    unfold nativeWholeLawErrorRadius
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (actualLowErrorComparisonConstant_nonneg M hTemp) (add_nonneg hR hsite),?_⟩
    convert Hfinal using 1
    rw [actualLowErrorComparisonConstant,mul_pow,mul_pow,
      Real.sq_sqrt (show 0 ≤ 2*Real.exp (220*M)*(Real.exp (110*Temp)+1) by positivity)]
    ring
  · have hlow : j<U:=not_not.mp hhigh
    rw [ite_eq_left hlow]
    have Hz : nativeWholeLawErrorSecond n as q A j=0 := by
      unfold nativeWholeLawErrorSecond A
      simp only [cutTSlope_zero_covariance,hlow,ite_true,
        Finset.sum_const_zero,zero_pow (by norm_num : (2:ℕ)≠0),ClockTree.disorderExpect,mul_zero]
    change Real.sqrt (nativeWholeLawErrorSecond n as q A j) ≤ 0
    rw [Hz,Real.sqrt_zero]

end OAI.SKFluctuations.Cavity
