module

public import SKConstants.Completion.N9Q2.NoiseRestart
public import SKConstants.Completion.N13a.PathRestriction

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace SKConstants.Completion.N9Q2
open SKConstantsOAI.ZeroTemperatureSK M1

theorem forwardPicard_restart (b : BoundedLipschitzDrift) (a v u : ℝ≥0) (hu : u ≤ v)
    (z : ℝ) (F : ScalarContinuousPath (a+v)) :
    scalarForwardPicardPath b (a+v) (z,F)
      ⟨a+u,(a+u).coe_nonneg,by exact_mod_cast (add_le_add le_rfl hu : a+u ≤ a+v)⟩ =
    scalarForwardPicardPath (SKConstants.BoundedLipschitzDrift.translated b a 0) v
      (scalarForwardPicardPath b (a+v) (z,F) ⟨a,a.coe_nonneg,by exact_mod_cast (le_self_add : a ≤ a+v)⟩,
        (scalarSplitPath a v F).2) ⟨u,u.coe_nonneg,hu⟩ := by
  let H := a+v
  let p := (z,F)
  let x := scalarForwardPicardPath b H p ⟨a,a.coe_nonneg,by exact_mod_cast (le_self_add : a ≤ a+v)⟩
  let C : ℝ≥0 → Unit → ℝ := fun s _ =>
    scalarContinuousSeedDriver H (a+s) p-scalarContinuousSeedDriver H a p
  have hc : Continuous (fun s => scalarContinuousSeedDriver H s p) :=
    (continuous_scalarContinuousSeedDriver H).comp (continuous_id.prodMk continuous_const)
  have hr := SKConstants.BoundedLipschitzDrift.solution_restart b (scalarPathFiltration H)
    (scalarContinuousSeedDriver H) (scalarContinuousSeedDriver_progressive H) p hc a u
  change b.solution (scalarContinuousSeedDriver H) (a+u) p = _
  rw [hr]
  change x+(SKConstants.BoundedLipschitzDrift.translated b a x).solution C u () = _
  rw [SKConstants.BoundedLipschitzDrift.solution_translated_add_seed]
  apply solution_congr_prefix (SKConstants.BoundedLipschitzDrift.translated b a 0)
    (fun s w => x+C s w) (scalarContinuousSeedDriver v)
    () (x,(scalarSplitPath a v F).2) v _ u hu
  intro s hs
  change x+(scalarContinuousSeedDriver H (a+s) p-scalarContinuousSeedDriver H a p) =
    x+(scalarSplitPath a v F).2 (projIcc 0 (v : ℝ) v.coe_nonneg s)
  have hsH : ((a+s : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (H : ℝ) :=
    ⟨(a+s).coe_nonneg,by exact_mod_cast (add_le_add le_rfl hs : a+s ≤ a+v)⟩
  have haH : (a : ℝ) ∈ Icc (0 : ℝ) (H : ℝ) := ⟨a.coe_nonneg,by exact_mod_cast (le_self_add : a ≤ a+v)⟩
  simp only [scalarContinuousSeedDriver,p,IccExtend,Function.comp_apply,
    projIcc_of_mem _ hsH,projIcc_of_mem _ haH,
    projIcc_of_mem _ ⟨s.coe_nonneg,hs⟩,scalarSplitPath,ContinuousMap.coe_mk]
  simp only [NNReal.coe_add,projIcc_of_mem _ ⟨s.coe_nonneg,hs⟩]
  simp only [coe_projIcc,min_eq_right (show (s : ℝ) ≤ (v : ℝ) from hs),
    max_eq_right s.coe_nonneg]
  ring_nf
  congr 2

theorem concat_restrict (a v : ℝ≥0) (B : ScalarContinuousPath a)
    (p : ScalarContinuousPath v) :
    scalarInitialAuxiliaryRestriction (a+v) a le_self_add (scalarConcatPath a v (B,p)) = B := by
  ext t
  simp only [scalarInitialAuxiliaryRestriction,scalarConcatPath,ContinuousMap.coe_mk,
    projIcc_of_mem _ t.property,
    projIcc_of_le_left v.coe_nonneg (sub_nonpos.mpr t.property.2)]
  ring

theorem twoDriverPicard_concat_at_start (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (a v : ℝ≥0) (z : ℝ) (B D : ScalarContinuousPath a)
    (p q : ScalarContinuousPath v) :
    scalarTwoDriverPicardPath b f g hf hg (a+v)
      (z,(scalarConcatPath a v (B,p),scalarConcatPath a v (D,q)))
      ⟨a,a.coe_nonneg,by exact_mod_cast (le_self_add : a ≤ a+v)⟩ =
      scalarTwoDriverPicardPath b f g hf hg a (z,(B,D)) ⟨a,a.coe_nonneg,le_rfl⟩ := by
  have h := N13a.coarsePrefix_twoDriverPicard b f g hf hg (a+v) a le_self_add z
    (scalarConcatPath a v (B,p)) (scalarConcatPath a v (D,q))
  rw [concat_restrict,concat_restrict] at h
  exact congrArg (fun F : ScalarContinuousPath a => F ⟨a,a.coe_nonneg,le_rfl⟩) h

theorem twoDriverPicard_concat_restart (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (a v u : ℝ≥0) (hu : u ≤ v) (z : ℝ) (B D : ScalarContinuousPath a)
    (p q : ScalarContinuousPath v)
    (hp : p ⟨0,le_rfl,v.coe_nonneg⟩ = 0) (hq : q ⟨0,le_rfl,v.coe_nonneg⟩ = 0) :
    scalarTwoDriverPicardPath b f g hf hg (a+v)
      (z,(scalarConcatPath a v (B,p),scalarConcatPath a v (D,q)))
      ⟨a+u,(a+u).coe_nonneg,by exact_mod_cast (add_le_add le_rfl hu : a+u ≤ a+v)⟩ =
    scalarForwardPicardPath (SKConstants.BoundedLipschitzDrift.translated b a 0) v
      (scalarTwoDriverPicardPath b f g hf hg a (z,(B,D)) ⟨a,a.coe_nonneg,le_rfl⟩,
        scalarTwoDriverWeightedPath (shiftedCoefficient f hf a) (shiftedCoefficient g hg a)
          (continuous_shiftedCoefficient f hf a) (continuous_shiftedCoefficient g hg a) v (p,q))
      ⟨u,u.coe_nonneg,hu⟩ := by
  unfold scalarTwoDriverPicardPath
  rw [forwardPicard_restart b a v u hu]
  have hx := twoDriverPicard_concat_at_start b f g hf hg a v z B D p q
  unfold scalarTwoDriverPicardPath at hx
  simp only [Prod.fst,Prod.snd] at hx ⊢
  rw [hx]
  congr 2
  apply Prod.ext
  · rfl
  · ext t
    exact twoDriver_concat_increment f g hf hg a v ⟨t,t.property.1⟩ t.property.2 B D p q hp hq

end SKConstants.Completion.N9Q2
