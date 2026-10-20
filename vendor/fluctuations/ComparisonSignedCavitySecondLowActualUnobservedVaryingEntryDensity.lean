module

public import ComparisonSignedCavitySecondLowUnobservedVaryingEntryProfile
public import ComparisonSignedCavityActualLowErrorDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 30000000

def nativeSecondLowMovingOriginalEntryRadius (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (i star U j : ℕ) : ℝ :=
  if j<U ∧ j≠i ∧ j≠star then
    nativeOriginalCutLowErrorRadius n b h as j+1/(n+1:ℕ) else 0

theorem actual_second_low_unobserved_varying_entry_density
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (C : ℝ) (hC : 0<C) (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) :
    ∀ᶠjGrid : ℕ in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as),
        U ≤ as.length → NativePersistentLowForks i star U T →
        partitionPoint 0 as U ≤ min (C*M.canonicalDirectTestBandScale) 1 →
      ∀s : T.Slot,
        ((nativeSecondLowUnobservedEntryRows T U 0).map (fun p=>|p.coeff| *
          nativeSecondLowMovingOriginalEntryRadius n M.bf M.hf as i star U
            (p.tree.splitIndex (p.embed s) p.mark))).sum ≤
          M.actualOriginalLowErrorDensitySaving C*M.xs^2+
            partitionPoint 0 as U/(n+1:ℕ) := by
  filter_upwards [M.actual_cut_low_error_edgeBudget_on_every_final_net C hC us hus] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro i star U T hU hpersistent hmass s
  let as:=finiteCutMasses us jGrid
  let f:=nativeSecondLowMovingOriginalEntryRadius n M.bf M.hf as i star U
  let R:=nativeOriginalCutLowErrorRadius n M.bf M.hf as
  let site:=(1/(n+1:ℕ):ℝ)
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hf:∀j,0 ≤ f j:=by
    intro j
    dsimp only [f,nativeSecondLowMovingOriginalEntryRadius]
    split_ifs
    · exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
    · exact le_rfl
  have hfi:f i=0:=by simp [f,nativeSecondLowMovingOriginalEntryRadius]
  have hfstar:f star=0:=by simp [f,nativeSecondLowMovingOriginalEntryRadius]
  have hfhigh:∀j,U ≤ j → f j=0:=by
    intro j hj
    simp [f,nativeSecondLowMovingOriginalEntryRadius,not_lt.mpr hj]
  have Hentry:=hpersistent.unobserved_moving_entry_split_profile_le_edgeBudget s hU ho f hf hfi hfstar hfhigh
  have Hmono:=actual_low_edgeBudget_mono ho (show ∀j,j ≤ as.length →
      f j ≤ if j<U then R j+site else 0 by
    intro j _hj
    dsimp only [f,nativeSecondLowMovingOriginalEntryRadius,R,site]
    by_cases Hj : j<U
    · simp only [Hj,true_and,ite_true]
      split_ifs
      · exact le_rfl
      · exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
    · simp only [Hj,false_and,ite_false,le_refl])
  have Heq:(fun j=>if j<U then R j+site else 0)=
      (fun j=>(1:ℝ)*(if j<U then R j else 0)+site*(if j<U then (1:ℝ) else 0)):=by
    funext j
    split_ifs <;> ring
  rw [Heq,actual_low_edgeBudget_linear,one_mul] at Hmono
  have Hones:edgeBudget 0 as (fun j=>if j<U then (1:ℝ) else 0)=partitionPoint 0 as U:=by
    rw [native_low_edgeBudget_eq_prefix_cells as 0 U hU,massCellSum_const,massPartition_take_end]
    simp
  rw [Hones] at Hmono
  apply Hentry.trans (Hmono.trans _)
  have HD:=hgrid U hU hmass
  have HH:=add_le_add_right HD (site*partitionPoint 0 as U)
  convert HH using 1 <;> dsimp [site] <;> ring

end OAI.SKFluctuations.Cavity
