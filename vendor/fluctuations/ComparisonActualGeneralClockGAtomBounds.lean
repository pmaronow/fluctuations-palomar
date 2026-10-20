module

public import ComparisonActualGeneralClockTerminalGAtom

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
theorem actual_general_clock_high_g_atom_abs_le_of_total_clock
    {n : ℕ} {Temp : ℝ}
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (a c e f : T.Slot) (σ : T.Assignment) :
    |actualGeneralClockHighGAtom bf hf K T U a c e f σ| ≤ 2*Temp := by
  have Htotal:=htotal _ (partitionPoint_mem as ho (T.splitIndex e f))
  have Hbond : (bf (partitionPoint 0 as (T.splitIndex e f)):ℝ) ≤ Temp := by
    linarith [(hf (partitionPoint 0 as (T.splitIndex e f))).coe_nonneg]
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  change |nativeOriginalHighGAtom T U K b
    (nativePhysicalResourceCenter n bf hf as) a c e f σ| ≤ _
  exact native_original_high_g_atom_abs_le T ho U K b
    (nativePhysicalResourceCenter n bf hf as) a c e f hTemp
    (by rw [abs_of_nonneg (NNReal.coe_nonneg _)];exact Hbond)
    (native_physical_resource_center_abs_le_one n bf hf hbf hhf as ho _) σ

theorem actual_general_clock_high_g_atom_second_moment_le_of_total_clock
    {n : ℕ} {Temp : ℝ}
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (a c e f : T.Slot) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(actualGeneralClockHighGAtom bf hf K T U a c e f σ)^2) x ≤ (2*Temp)^2 := by
  have hw:=T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q x
  unfold ClockTree.disorderExpect
  calc
    _ ≤ ∑σ : T.Assignment,T.disorderWeight (fullWeight n) (fullFeature n) v q σ x*(2*Temp)^2 := by
      apply Finset.sum_le_sum
      intro σ _
      have H:=actual_general_clock_high_g_atom_abs_le_of_total_clock bf hf K hbf hhf hTemp htotal T ho U a c e f σ
      have Hsq:=(sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2*Temp)).mpr H
      rw [sq_abs] at Hsq
      exact mul_le_mul_of_nonneg_left Hsq (hw.1 σ)
    _=(2*Temp)^2 := by rw [←Finset.sum_mul,hw.2,one_mul]

theorem NativeOriginalGMarkedWord.actual_general_clock_second_moment_le_of_total_clock
    {n : ℕ} {Temp : ℝ}
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (ho : MassOrdered 0 as) (U : ℕ) (a : T.Slot)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) :
    g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(g.physicalClockAtom bf hf K U a σ)^2) x ≤ (2*Temp)^2 :=
  actual_general_clock_high_g_atom_second_moment_le_of_total_clock bf hf K hbf hhf hTemp htotal g.tree ho U _ _ _ _ v q x

end OAI.SKFluctuations.Cavity
