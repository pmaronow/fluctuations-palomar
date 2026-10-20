module

public import ComparisonSignedCavityOriginalHighProfileYoung

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem nativeOriginalGMarkedWords_forkLedger {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (f : ℕ→ℝ) :
    ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *g.tree.forkCost f)).sum=
      forkLedger 0 f 3 T := by
  dsimp only [NativeOriginalGMarkedWord.coefficient,NativeOriginalGMarkedWord.tree]
  rw [nativeOriginalGMarkedWords_kernel_sum T
    (fun p r z=>|p.coeff*r.coeff*z.coeff| *z.tree.forkCost f)]
  simp only [abs_mul,forkLedger,List.sum_map_mul_left,mul_assoc]

theorem nativeOriginalGMarkedWords_forkProfile_le {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (f : ℕ→ℝ)
    (hf : ∀j,0≤f j) (r : ℕ) (hr : T.leaves≤r) :
    ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *g.tree.forkCost f)).sum≤
      forkVariation r 3*(T.forkCost f+edgeBudget 0 as f) := by
  rw [nativeOriginalGMarkedWords_forkLedger]
  exact T.forkLedger_le ho hf hr 3

theorem nativeOriginalGMarkedWords_wholeProfile_le {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (f : ℕ→ℝ)
    (hf : ∀j,0≤f j) (r : ℕ) (hr : T.leaves≤r) :
    ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *
      (g.tree.forkCost f+edgeBudget 0 as f))).sum≤
      (forkVariation r 3+8*(r:ℝ)*(r+1)*(r+2))*(T.forkCost f+edgeBudget 0 as f) := by
  simp only [mul_add,List.sum_map_add,List.sum_map_mul_right]
  have HF:=nativeOriginalGMarkedWords_forkProfile_le T ho f hf r hr
  have HV:=nativeOriginalGMarkedWords_variation_le T ho r hr
  have HE:=edgeBudget_nonneg ho hf
  have HT:=T.forkCost_nonneg hf
  have HB:=mul_le_mul_of_nonneg_right HV HE
  have Hextra:=mul_nonneg (show 0≤8*(r:ℝ)*(r+1)*(r+2) by positivity) HT
  nlinarith

end OAI.SKFluctuations.Cavity
