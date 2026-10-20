module

public import ComparisonShiftedNativeRadiusCells
public import ComparisonNativeRadiusHeightBins

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

def radiusRowMass {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1))) (a z : ℝ)
    (i : Fin ((sampleClockSteps clock 0 as).length+1)) : ℝ :=
  if i∈J then volume.real (Ioo a z∩Ioc
    (m.R (physicalCutMass 0 (sampleClockSteps clock 0 as) i.val))
    (m.R (physicalCutMass 0 (sampleClockSteps clock 0 as) (i.val+1)))) else 0

theorem radiusRowMass_nonneg {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1))) (a z : ℝ)
    (i : Fin ((sampleClockSteps clock 0 as).length+1)) :
    0 ≤ radiusRowMass m clock as J a z i := by
  unfold radiusRowMass
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem radiusRowMass_zero_of_zero_mass {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1))) (a z : ℝ)
    (i : Fin ((sampleClockSteps clock 0 as).length+1))
    (hi : pathMassDifferences (sampleClockSteps clock 0 as) 0 i=0) :
    radiusRowMass m clock as J a z i=0 := by
  rw [pathMassDifferences_eq_cutMass] at hi
  have he := sub_eq_zero.mp hi
  simp only [radiusRowMass,he,Ioc_self,inter_empty,measureReal_empty,ite_self]

theorem radiusRowMass_le_mesh {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    {a z : ℝ} (haz : a ≤ z) (i : Fin ((sampleClockSteps clock 0 as).length+1)) :
    radiusRowMass m clock as J a z i ≤ mesh/m.c := by
  let steps := sampleClockSteps clock 0 as
  let R := m.R
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  have hmass : physicalCutMass 0 steps i.val ≤ physicalCutMass 0 steps (i.val+1) :=
    physicalCutMass_monotone steps hs (Nat.le_succ _)
  have hR : R (physicalCutMass 0 steps i.val) ≤ R (physicalCutMass 0 steps (i.val+1)) :=
    m.R_monotone hmass
  have hLip := (m.R_lipschitz).dist_le_mul
    (physicalCutMass 0 steps (i.val+1)) (physicalCutMass 0 steps i.val)
  change dist (R (physicalCutMass 0 steps (i.val+1))) (R (physicalCutMass 0 steps i.val)) ≤
    (1/m.c)*dist (physicalCutMass 0 steps (i.val+1)) (physicalCutMass 0 steps i.val) at hLip
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hR),
    abs_of_nonneg (sub_nonneg.mpr hmass)] at hLip
  have hbound := sampled_physicalMass_mesh clock as hmesh i
  have hwidth : R (physicalCutMass 0 steps (i.val+1))-R (physicalCutMass 0 steps i.val) ≤ mesh/m.c :=
    hLip.trans (by simpa only [steps,div_eq_mul_inv,one_mul,mul_one,mul_comm] using
      mul_le_mul_of_nonneg_left hbound (one_div_nonneg.mpr m.hc.le))
  unfold radiusRowMass
  split_ifs
  · exact (NativeRadiusHeight.clipped_radius_cell_mass_le haz hR).2.trans hwidth
  · exact div_nonneg hmesh0 m.hc.le

theorem radiusRows_strip_budget {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh δ a z : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (hδ : 0 ≤ δ) (haz : a ≤ z)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1))) :
    let v := radiusRowMass m clock as J a z
    (∑i,if i∉NativeRadiusHeight.retainedRows v δ then v i else 0) ≤ 2*δ+2*(mesh/m.c) ∧
      (∀i∈NativeRadiusHeight.retainedRows v δ,
        δ ≤ NativeRadiusHeight.leftMass v i ∧ δ ≤ NativeRadiusHeight.rightMass v i) := by
  dsimp only
  refine ⟨NativeRadiusHeight.omitted_radius_mass_le _
    (radiusRowMass_nonneg m clock as J a z)
    hδ (div_nonneg hmesh0 m.hc.le)
    (radiusRowMass_le_mesh m clock as ho hmesh hmesh0 J haz),?_⟩
  intro i hi
  exact NativeRadiusHeight.retained_side_lengths _ δ hi

theorem radiusRowMass_total {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {a z : ℝ} (ha : m.rmin ≤ a) (haz : a ≤ z) (hz : z ≤ 1) :
    (∑i,radiusRowMass m clock as Finset.univ a z i)=z-a := by
  let steps := sampleClockSteps clock 0 as
  let R := m.R
  let cuts := fun j=>NativeRadiusHeight.clippedRadiusCut a z (R (physicalCutMass 0 steps j))
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  have hcutsMono : Monotone (physicalCutMass 0 steps) := physicalCutMass_monotone steps hs
  have hR : Monotone R := m.R_monotone
  have hv (i : Fin (steps.length+1)) :
      radiusRowMass m clock as Finset.univ a z i=
        cuts (i.val+1)-cuts i.val := by
    simpa only [radiusRowMass,Finset.mem_univ,ite_true] using
      NativeRadiusHeight.volume_clipped_radius_cell haz (hR (hcutsMono (Nat.le_succ i.val)))
  have hh := NativeRadiusHeight.finite_cell_prefix_sum cuts (steps.length+1) le_rfl
  simp only [Fin.is_lt,ite_true] at hh
  have he := And.intro (m.R_before m.hu.1) m.R_one
  have hstart : cuts 0=a := by
    simp only [cuts,R,physicalCutMass,he.1,NativeRadiusHeight.clippedRadiusCut,
      min_eq_right (ha.trans haz),max_eq_left ha]
  have hend : cuts (steps.length+1)=z := by
    change NativeRadiusHeight.clippedRadiusCut a z (R (physicalCutMass 0 steps (steps.length+1)))=z
    rw [physicalCutMass_terminal]
    simp only [R,he.2,NativeRadiusHeight.clippedRadiusCut,min_eq_left hz,max_eq_right haz]
  simp_rw [hv]
  rw [hh,hstart,hend]

theorem radiusHeightBins_mass_partition {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (S : Fin ((sampleClockSteps clock 0 as).length+1)→ℝ) {bins : ℕ} (hk0 : 0<bins)
    (w a z : ℝ) :
    (∑b : Fin bins,∑i,radiusRowMass m clock as
      (NativeRadiusHeight.bin S J w b) a z i)=
      ∑i,radiusRowMass m clock as J a z i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  unfold radiusRowMass NativeRadiusHeight.bin
  simp only [Finset.mem_filter]
  by_cases hi : i∈J
  · let b0 : Fin bins := ⟨heightBin bins w (S i),heightBin_lt hk0 _ _⟩
    have hb (b : Fin bins) : heightBin bins w (S i)=b.val ↔ b=b0 := by
      constructor
      · intro he;exact Fin.ext he.symm
      · intro he;subst b;rfl
    simp only [hi,true_and,ite_true]
    simp_rw [hb]
    simp
  · simp only [hi,false_and,ite_false,Finset.sum_const_zero]

theorem radiusHeightBins_strip_budget {ι : Type}
    (clock : ℝ→ι→ℝ≥0) 
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh δ a z : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (hδ : 0 ≤ δ) (haz : a ≤ z)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (S : Fin ((sampleClockSteps clock 0 as).length+1)→ℝ) (bins : ℕ) (w : ℝ) :
    (∑b : Fin bins,
      let v := radiusRowMass m clock as
        (NativeRadiusHeight.bin S J w b) a z
      ∑i,if i∉NativeRadiusHeight.retainedRows v δ then v i else 0) ≤
      2*(bins:ℝ)*δ+2*(bins:ℝ)*(mesh/m.c) := by
  have hh := Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin bins))) (fun b _=>
    (radiusRows_strip_budget m clock as ho
      hmesh hmesh0 hδ haz (NativeRadiusHeight.bin S J w b)).1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  convert hh using 1; ring

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
