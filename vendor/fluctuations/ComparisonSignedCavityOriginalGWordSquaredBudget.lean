module

public import ComparisonSignedCavityOriginalGWordProfileLedger

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem nativeOriginalGWordRestorationCost_le_squared_profiles
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (ho : MassOrdered 0 as)
    (U r : ℕ) (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ) (a : T.Slot)
    (Mclock Temp p CH CL rho : ℝ) (hTemp : 0≤Temp) (hCH : 0≤CH) (hCL : 0≤CL) (hrho : 0≤rho) :
    let R:=nativeOriginalHighErrorEnvelope n U bf hf as Mclock Temp
    let f:=fun j=>(R j)^(2/p)
    let AH:=pairForkVariation r*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)
    let AL:=absJetVariation r 1*CL*rho
    nativeOriginalGWordRestorationCost g U r bf hf K a Mclock Temp p CH CL rho ≤
      AH*((g.tree.leaves:ℝ)+1)*(g.tree.forkCost (fun j=>(f j)^2)+edgeBudget 0 as (fun j=>(f j)^2))+
      AL*g.tree.forkCost R := by
  dsimp only
  let R:=nativeOriginalHighErrorEnvelope n U bf hf as Mclock Temp
  let f:=fun j=>(R j)^(2/p)
  let AH:=pairForkVariation r*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)
  let AL:=absJetVariation r 1*CL*rho
  have hR j : 0≤R j := by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf j : 0≤f j:=Real.rpow_nonneg (hR j) _
  have hAH : 0≤AH := by
    dsimp only [AH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg r) hCH)
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  have hAL : 0≤AL:=mul_nonneg (mul_nonneg (absJetVariation_nonneg r 1) hCL) hrho
  have hP : 0≤g.tree.forkCost (fun j=>(f j)^2)+edgeBudget 0 as (fun j=>(f j)^2):=
    add_nonneg (g.tree.forkCost_nonneg (fun j=>sq_nonneg (f j)))
      (edgeBudget_nonneg ho (fun j=>sq_nonneg (f j)))
  by_cases hdiag : g.z.embed g.r.mark=g.z.mark
  · rw [nativeOriginalGWordRestorationCost,ite_eq_left hdiag]
    exact add_nonneg (mul_nonneg (mul_nonneg hAH (by positivity)) hP)
      (mul_nonneg hAL (g.tree.forkCost_nonneg hR))
  · let j:=g.tree.splitIndex (g.z.embed g.r.mark) g.z.mark
    let κ:=|(1/2:ℝ)*fullScalarCutConnected4 g.tree U K
      (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
      (g.z.embed g.r.mark) g.z.mark|
    have hκ : κ≤1 := by
      have H:=native_full_scalar_connected_four_abs_le_two g.tree ho U K
        (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
        (g.z.embed g.r.mark) g.z.mark
      dsimp only [κ]
      rw [abs_mul]
      norm_num only [abs_of_nonneg (show (0:ℝ)≤1/2 by norm_num)]
      linarith
    have HY:=native_distinct_pair_profile_product_le g.tree ho f _ _ hdiag
    have HS:=g.tree.split_le_forkCost hR _ _ hdiag
    have HI : 0≤AH*(f j*(g.tree.forkCost f+edgeBudget 0 as f))+AL*R j := by
      exact add_nonneg (mul_nonneg hAH (mul_nonneg (hf j)
        (add_nonneg (g.tree.forkCost_nonneg hf) (edgeBudget_nonneg ho hf)))) (mul_nonneg hAL (hR j))
    calc
      _=κ*(AH*(f j*(g.tree.forkCost f+edgeBudget 0 as f))+AL*R j) := by
        rw [nativeOriginalGWordRestorationCost,ite_eq_right hdiag]
        dsimp only [κ,AH,AL,f,j,R]
        ring
      _≤AH*(f j*(g.tree.forkCost f+edgeBudget 0 as f))+AL*R j :=
        mul_le_of_le_one_left HI hκ
      _≤_ := by
        have H1:=mul_le_mul_of_nonneg_left HY hAH
        have H2:=mul_le_mul_of_nonneg_left HS hAL
        change _≤AH*((g.tree.leaves:ℝ)+1)*_+AL*g.tree.forkCost R
        dsimp only [j] at HI ⊢
        nlinarith

end OAI.SKFluctuations.Cavity
