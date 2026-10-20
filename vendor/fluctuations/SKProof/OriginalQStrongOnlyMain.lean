module

public import SKProof.OriginalQWeakExclusion
public import SKProof.OriginalQMacroWeakExclusion
public import SKProof.OriginalQPhysicalExclusionsMain

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open Set Filter Hierarchy
open scoped Topology NNReal
open OriginalQFixedTStoppingDraft OriginalQPhysicalReducedDraft

def ActualOriginalQStrongExclusionInputs : Prop :=
  ∀ T m cl cu : ℝ, 1 < T → 0 < m → m < 1/300 → 0 < cl → 0 < cu →
    cl < T*Real.exp (-12*T) →
    T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu →
    ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
      (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
        m (m/10000) cl cu 2 1 1 1 T),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      Tendsto (fun n => (Q n).xs) atTop (𝓝 0) →
      ∀ eta : ℝ, 0 < eta → ∀ phi : ℕ → ℕ, StrictMono phi →
        (∀ n, eta ≤ laplaceComparisonStrength
          (Q (phi n)).data.d (Q (phi n)).lam (Q (phi n)).xs /
          (Q (phi n)).xs^2) → False

theorem actualOriginalQPhysicalExclusionInputs_of_strong :
    ActualOriginalQStrongExclusionInputs → ActualOriginalQPhysicalExclusionInputs := by
  intro Hstrong beta hbeta m hm hmmax
  let T : ℝ := beta^2
  have hT : 1 < T := by
    dsimp only [T]
    nlinarith only [hbeta]
  obtain ⟨lowerW, upperW, hlowerW, _hupperW, Hweak⟩ :=
    exists_weak_exclusion_original_q hT hm hmmax
  obtain ⟨lowerM, upperM, hlowerM, _hupperM, Hmacro⟩ :=
    exists_macro_weak_exclusion_original_q hT hm hmmax
  let a : ℝ := T*Real.exp (-12*T)
  let b : ℝ := T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T))
  have ha : 0 < a := mul_pos (zero_lt_one.trans hT) (Real.exp_pos _)
  let cl : ℝ := min (min lowerW lowerM) (min 1 (a/2))
  let cu : ℝ := max (max upperW upperM) (max 1 (b+1))
  have hcl : 0 < cl := lt_min (lt_min hlowerW hlowerM)
    (lt_min zero_lt_one (half_pos ha))
  have hclW : cl ≤ lowerW := (min_le_left _ _).trans (min_le_left _ _)
  have hclM : cl ≤ lowerM := (min_le_left _ _).trans (min_le_right _ _)
  have hcl1 : cl ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hclTemp : cl < T*Real.exp (-12*T) := by
    have hhalf : cl ≤ a/2 := (min_le_right _ _).trans (min_le_right _ _)
    change cl < a
    linarith only [hhalf, ha]
  have hcuW : upperW ≤ cu := (le_max_left _ _).trans (le_max_left _ _)
  have hcuM : upperM ≤ cu := (le_max_right _ _).trans (le_max_left _ _)
  have hcu1 : 1 ≤ cu := (le_max_left _ _).trans (le_max_right _ _)
  have hcu : 0 < cu := zero_lt_one.trans_le hcu1
  have hcuTemp : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu := by
    have hbound : b+1 ≤ cu := (le_max_right _ _).trans (le_max_right _ _)
    change b < cu
    linarith only [hbound]
  refine ⟨cl, cu, hcl, hcl1, hcu1, ?_⟩
  exact {
    hT := hT
    hm := hm
    hmmax := hmmax
    hcl := hcl
    hcl1 := hcl1
    hcu1 := hcu1
    macroWeak := Hmacro cl cu hcl hclM hcuM hclTemp hcuTemp
    strong := Hstrong T m cl cu hT hm hmmax hcl hcu hclTemp hcuTemp
    weak := Hweak cl cu hcl hclW hcuW hclTemp hcuTemp }

theorem main_fluctuation_statement_of_strong_exclusion :
    ActualOriginalQStrongExclusionInputs → OAI.SKFluctuations.MainFluctuationStatement := by
  intro Hstrong
  exact main_fluctuation_statement_of_physical_exclusions
    (actualOriginalQPhysicalExclusionInputs_of_strong Hstrong)

end OAI.SKFluctuations.LaplaceWindowFormalization
