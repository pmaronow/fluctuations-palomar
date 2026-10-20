module

public import ComparisonSignedCavityOriginalGWordSquaredBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeOriginalRestorationProfileVariation (r : ℕ) : ℝ :=
  ((r:ℝ)+4)*(forkVariation r 3+8*(r:ℝ)*(r+1)*(r+2))

theorem nativeOriginalRestorationProfileVariation_nonneg (r : ℕ) :
    0≤nativeOriginalRestorationProfileVariation r := by
  unfold nativeOriginalRestorationProfileVariation
  exact mul_nonneg (by positivity) (add_nonneg (forkVariation_nonneg r 3) (by positivity))

theorem native_original_G_word_restoration_sum_le_profiles
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U rCost r : ℕ) (hr : T.leaves≤r)
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ) (a : T.Slot)
    (Mclock Temp p CH CL rho : ℝ) (hTemp : 0≤Temp) (hCH : 0≤CH) (hCL : 0≤CL) (hrho : 0≤rho) :
    let R:=nativeOriginalHighErrorEnvelope n U bf hf as Mclock Temp
    let f2:=fun j=>((R j)^(2/p))^2
    let AH:=pairForkVariation rCost*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)
    let AL:=absJetVariation rCost 1*CL*rho
    ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *
      nativeOriginalGWordRestorationCost g U rCost bf hf K a Mclock Temp p CH CL rho)).sum≤
      AH*nativeOriginalRestorationProfileVariation r*(T.forkCost f2+edgeBudget 0 as f2)+
      AL*forkVariation r 3*(T.forkCost R+edgeBudget 0 as R) := by
  dsimp only
  let R:=nativeOriginalHighErrorEnvelope n U bf hf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let AH:=pairForkVariation rCost*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)
  let AL:=absJetVariation rCost 1*CL*rho
  have hR j : 0≤R j := by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0≤f2 j:=sq_nonneg _
  have hAH : 0≤AH := by
    dsimp only [AH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg rCost) hCH)
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  have hAL : 0≤AL:=mul_nonneg (mul_nonneg (absJetVariation_nonneg rCost 1) hCL) hrho
  have Hg (g : NativeOriginalGMarkedWord T) :
      nativeOriginalGWordRestorationCost g U rCost bf hf K a Mclock Temp p CH CL rho≤
        AH*((r:ℝ)+4)*(g.tree.forkCost f2+edgeBudget 0 as f2)+AL*g.tree.forkCost R := by
    have H:=nativeOriginalGWordRestorationCost_le_squared_profiles g ho U rCost bf hf K a
      Mclock Temp p CH CL rho hTemp hCH hCL hrho
    have H1:=T.markedAttach_leaves 0 g.p g.hp
    have H2:=g.p.tree.markedAttach_leaves 0 g.r g.hr
    have H3:=g.r.tree.markedAttach_leaves 0 g.z g.hz
    have Hleaves : g.tree.leaves≤r+3 := by dsimp only [NativeOriginalGMarkedWord.tree];omega
    have Hcast : (g.tree.leaves:ℝ)+1≤(r:ℝ)+4 := by
      have HH : (g.tree.leaves:ℝ)≤(r+3:ℕ):=by exact_mod_cast Hleaves
      simp only [Nat.cast_add,Nat.cast_ofNat] at HH
      linarith
    have Hprofile:=add_nonneg (g.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)
    apply H.trans
    change AH*((g.tree.leaves:ℝ)+1)*_+AL*g.tree.forkCost R≤_
    exact add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hcast hAH) Hprofile) (le_refl _)
  have Hsum : ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *
      nativeOriginalGWordRestorationCost g U rCost bf hf K a Mclock Temp p CH CL rho)).sum≤
      AH*((r:ℝ)+4)*((nativeOriginalGMarkedWords T).map
        (fun g=>|g.coefficient| *(g.tree.forkCost f2+edgeBudget 0 as f2))).sum+
      AL*((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *g.tree.forkCost R)).sum := by
    calc
      _≤((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *
        (AH*((r:ℝ)+4)*(g.tree.forkCost f2+edgeBudget 0 as f2)+AL*g.tree.forkCost R))).sum := by
        apply List.sum_le_sum
        intro g hg
        exact mul_le_mul_of_nonneg_left (Hg g) (abs_nonneg _)
      _=_ := by
        simp only [←List.sum_map_mul_left,←List.sum_map_add]
        congr 1
        apply List.map_congr_left
        intro g hg
        ring
  have Hhigh:=nativeOriginalGMarkedWords_wholeProfile_le T ho f2 hf2 r hr
  have Hlow:=nativeOriginalGMarkedWords_forkProfile_le T ho R hR r hr
  have hCoeff : 0≤AH*((r:ℝ)+4):=mul_nonneg hAH (by positivity)
  have HH:=add_le_add
    (mul_le_mul_of_nonneg_left Hhigh hCoeff)
    (mul_le_mul_of_nonneg_left Hlow hAL)
  apply Hsum.trans
  simpa only [nativeOriginalRestorationProfileVariation,AH,AL,f2,R,mul_assoc] using HH

end OAI.SKFluctuations.Cavity
