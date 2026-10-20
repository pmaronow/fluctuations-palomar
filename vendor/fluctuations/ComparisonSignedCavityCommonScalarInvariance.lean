module

public import CavitySpinRelabel
public import CavityCompletedScalar

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree

theorem assignment_subsingleton {S : Type*} [Subsingleton S]
    {as : List PositiveMass} (T : ClockTree S as) : Subsingleton T.Assignment := by
  induction T with
  | leaf => exact inferInstance
  | step a T ih => exact ih
  | fork T U ihT ihU =>
    let := ihT
    let := ihU
    exact inferInstance

theorem assignment_nonempty {S : Type*} [Nonempty S]
    {as : List PositiveMass} (T : ClockTree S as) : Nonempty T.Assignment := by
  induction T with
  | leaf => exact inferInstance
  | step a T ih => exact ih
  | fork T U ihT ihU =>
    let := ihT
    let := ihU
    exact inferInstance

theorem disorderExpect_common_scalar_invariant
    {S ι κ : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Fintype κ]
    {w : S → ℝ} (hw : ∀s,0 < w s) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (χ : (κ → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (q r : ℕ → ι ⊕ κ → ℝ) (hqr : ∀j i,q j (.inl i)=r j (.inl i))
    (P : T.Assignment → ℝ) :
    T.disorderExpect w (fun s => (φ s).comp sumLeft+χ.comp sumRight) 0 q P 0 =
      T.disorderExpect w (fun s => (φ s).comp sumLeft+χ.comp sumRight) 0 r P 0 := by
  let e : S ≃ S×Unit := (Equiv.prodUnique S Unit).symm
  let R := T.relabelSpin e
  let A := T.relabelAssignment e
  let : Subsingleton R.cavityRight.Assignment := R.cavityRight.assignment_subsingleton
  let z : R.cavityRight.Assignment := Classical.choice R.cavityRight.assignment_nonempty
  let F : R.cavityLeft.Assignment → ℝ := fun σ => P (A.symm (R.cavityAssignment.symm (σ,z)))
  have hF (σ : R.Assignment) : F (R.cavityAssignment σ).1=P (A.symm σ) := by
    have hz : ((R.cavityAssignment σ).1,z)=R.cavityAssignment σ := by
      ext
      · rfl
      · exact Subsingleton.elim _ _
    dsimp only [F]
    rw [hz,Equiv.symm_apply_apply]
  have htransfer (c : ℕ → ι ⊕ κ → ℝ) :
      T.disorderExpect w (fun s => (φ s).comp sumLeft+χ.comp sumRight) 0 c P 0 =
        R.cavityLeft.disorderExpect w φ 0 (fun j i => c j (.inl i)) F 0 := by
    have H := T.disorderExpect_relabelSpin e (fun s : S×Unit => w s.1*(1:ℝ))
      (productFeature φ (fun _ : Unit => χ)) 0 c (fun σ => P (A.symm σ)) 0
    have HF := R.disorderExpect_cavity_product hw (fun _ : Unit => zero_lt_one)
      φ (fun _ : Unit => χ) ho 0 c F (fun _ => 1) 0
    simp only [mul_one,Pi.zero_apply] at HF
    simp_rw [hF] at HF
    rw [R.cavityRight.disorderExpect_one (fun _ : Unit => zero_lt_one) (fun _ : Unit => χ) ho,
      mul_one] at HF
    have Hleft :
        T.disorderExpect w (fun s => (φ s).comp sumLeft+χ.comp sumRight) 0 c P 0 =
          R.disorderExpect (fun s : S×Unit => w s.1) (productFeature φ (fun _ : Unit => χ))
            0 c (fun σ => P (A.symm σ)) 0 := by
      simpa only [e,Function.comp_def,Equiv.prodUnique_symm_apply,productFeature,mul_one,
        Equiv.symm_apply_apply,A] using H
    exact Hleft.trans HF
  rw [htransfer q,htransfer r]
  congr 1
  exact funext (fun j => funext (hqr j))

end OAI.SKFluctuations.Hierarchy.ClockTree
