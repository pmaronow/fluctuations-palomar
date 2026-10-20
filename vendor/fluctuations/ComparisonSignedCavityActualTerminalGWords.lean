module

public import ComparisonSignedCavityActualTerminalGAtom
public import ComparisonSignedCavityThreeRowVariation

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

def nativeOriginalGMarkedWords {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) : List (NativeOriginalGMarkedWord T) :=
  (T.markedAttach 0).attach.flatMap (fun p=>
    (p.val.tree.markedAttach 0).attach.flatMap (fun r=>
      (r.val.tree.markedAttach 0).attach.map (fun z=>
        ⟨p.val,p.property,r.val,r.property,z.val,z.property⟩)))

def NativeOriginalGMarkedWord.coefficient {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (g : NativeOriginalGMarkedWord T) : ℝ :=
  g.p.coeff*g.r.coeff*g.z.coeff

theorem nativeOriginalGMarkedWords_kernel_sum {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) → MarkedPlacement r.tree → ℝ) :
    ((nativeOriginalGMarkedWords T).map (fun g=>F g.p g.r g.z)).sum=
      ((T.markedAttach 0).map (fun p=>
        ((p.tree.markedAttach 0).map (fun r=>
          ((r.tree.markedAttach 0).map (fun z=>F p r z)).sum)).sum)).sum := by
  simp only [nativeOriginalGMarkedWords,List.map_flatMap,native_sum_flatMap,List.map_map,
    List.attach_map_val,Function.comp_def]
  conv_rhs => rw [←List.attach_map_val]
  congr 1
  apply List.map_congr_left
  intro p hp
  conv_rhs => rw [←List.attach_map_val]

theorem nativeOriginalGMarkedWords_weighted_kernel_sum {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) → MarkedPlacement r.tree → ℝ) :
    ((nativeOriginalGMarkedWords T).map (fun g=>g.coefficient*F g.p g.r g.z)).sum=
      ((T.markedAttach 0).map (fun p=>p.coeff*
        ((p.tree.markedAttach 0).map (fun r=>r.coeff*
          ((r.tree.markedAttach 0).map (fun z=>z.coeff*F p r z)).sum)).sum)).sum := by
  unfold NativeOriginalGMarkedWord.coefficient
  rw [nativeOriginalGMarkedWords_kernel_sum T (fun p r z=>p.coeff*r.coeff*z.coeff*F p r z)]
  simp only [List.sum_map_mul_left,mul_assoc]

private def rowAbsSign (c : ℝ) : ℝ := if c < 0 then -1 else 1

private theorem rowAbsSign_abs (c : ℝ) : |rowAbsSign c|=1 := by
  unfold rowAbsSign
  split_ifs <;> norm_num

private theorem rowAbsSign_mul (c : ℝ) : c*rowAbsSign c=|c| := by
  unfold rowAbsSign
  split_ifs with hc
  · rw [abs_of_neg hc];ring
  · rw [abs_of_nonneg (le_of_not_gt hc),mul_one]

private theorem rowSignProduct (a b c : ℝ) :
    a*(b*(c*(rowAbsSign a*rowAbsSign b*rowAbsSign c)))=|a*b*c| := by
  calc
    _=(a*rowAbsSign a)*(b*rowAbsSign b)*(c*rowAbsSign c) := by ring
    _=_ := by rw [rowAbsSign_mul,rowAbsSign_mul,rowAbsSign_mul,abs_mul,abs_mul]

theorem nativeOriginalGMarkedWords_variation {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) :
    ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient|)).sum≤
      8*(T.leaves:ℝ)*(T.leaves+1)*(T.leaves+2) := by
  have H:=marked_three_row_abs_le T ho
    (fun p r z=>rowAbsSign p.coeff*rowAbsSign r.coeff*rowAbsSign z.coeff)
    (D:=1) zero_le_one (by
      intro p hp r hr z hz
      simp only [abs_mul,rowAbsSign_abs,mul_one,le_refl])
  simp only [←List.sum_map_mul_left,rowSignProduct,mul_one] at H
  rw [←nativeOriginalGMarkedWords_kernel_sum T (fun p r z=>|p.coeff*r.coeff*z.coeff|)] at H
  have Hpos : 0≤((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient|)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨g,hg,rfl⟩:=List.mem_map.mp hx
    exact abs_nonneg _
  dsimp only [NativeOriginalGMarkedWord.coefficient] at Hpos
  rw [abs_of_nonneg Hpos] at H
  exact H

theorem nativeOriginalGMarkedWords_variation_le {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (r : ℕ) (hr : T.leaves≤r) :
    ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient|)).sum≤
      8*(r:ℝ)*(r+1)*(r+2) := by
  have Hcast : (T.leaves:ℝ)≤r:=by exact_mod_cast hr
  apply (nativeOriginalGMarkedWords_variation T ho).trans
  exact mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left Hcast (by norm_num))
      (by linarith : (T.leaves:ℝ)+1≤(r:ℝ)+1) (by positivity) (by positivity))
    (by linarith : (T.leaves:ℝ)+2≤(r:ℝ)+2) (by positivity) (by positivity)

end OAI.SKFluctuations.Cavity
