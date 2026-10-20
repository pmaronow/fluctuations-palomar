module

public import ComparisonNativeKeptUnionMass
public import ComparisonNativeConstructedRows

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology ENNReal NNReal BigOperators
set_option maxHeartbeats 2200000
attribute [local instance] Classical.propDecidable

theorem native_height_bins_disjoint {N K bins : ℕ}
    (S : Fin N→ℝ) (J : Finset (Fin N)) (unit : Fin N→Fin K) (w : ℝ) :
    Pairwise (fun b c:Fin bins=>Disjoint (NativeUnitHeight.bin S J unit bins w b)
      (NativeUnitHeight.bin S J unit bins w c)) := by
  intro b c hbc
  apply Finset.disjoint_left.mpr
  intro i hib hic
  have hb := (Finset.mem_filter.mp hib).2
  have hc := (Finset.mem_filter.mp hic).2
  exact hbc (Fin.ext (hb.symm.trans hc))

theorem native_height_bins_union {N K bins : ℕ}
    (S : Fin N→ℝ) (J : Finset (Fin N)) (unit : Fin N→Fin K) (w : ℝ)
    (hbins : 0<bins) :
    Finset.univ.biUnion (NativeUnitHeight.bin S J unit bins w)=J := by
  ext i
  constructor
  · intro hi
    obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hb).1
  · intro hi
    obtain ⟨b,hb,_⟩ := NativeUnitHeight.bin_partition S J unit w hbins hi
    exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,hb⟩

theorem native_kept_disjoint_mass {ι : Type} {β : Type*} [Fintype β]
    (steps : List (GaussianStep ι)) (J : β→Finset (Fin (steps.length+1)))
    (keep : β→Bool) (hdisjoint : Pairwise (fun b c=>Disjoint (J b) (J c))) :
    physicalWindowMass steps 0 (nativeKeptRows J keep)=
      ∑b,if keep b then physicalWindowMass steps 0 (J b) else 0 := by
  have hd : ∀b∈(Finset.univ : Finset β),∀c∈(Finset.univ : Finset β),b≠c→
      Disjoint (if keep b then J b else ∅) (if keep c then J c else ∅) := by
    intro b _ c _ hbc
    split_ifs <;> first | exact hdisjoint hbc | simp
  rw [nativeKeptRows,physicalWindowMass,Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp only [physicalWindowMass,Finset.sum_empty]

theorem native_height_bins_mass_accounting {ι : Type} {bins : Type*} [Fintype bins]
    (steps : List (GaussianStep ι)) (A : Finset (Fin (steps.length+1)))
    (J : bins→Finset (Fin (steps.length+1))) (keep : bins→Bool)
    (hdisjoint : Pairwise (fun b c=>Disjoint (J b) (J c)))
    (hcover : Finset.univ.biUnion J=A) :
    physicalWindowMass steps 0 A=∑b,physicalWindowMass steps 0 (J b) ∧
    physicalWindowMass steps 0 (nativeKeptRows J keep)=
      (∑b,if keep b then physicalWindowMass steps 0 (J b) else 0) ∧
    physicalWindowMass steps 0 A-physicalWindowMass steps 0 (nativeKeptRows J keep)=
      ∑b,if keep b then 0 else physicalWindowMass steps 0 (J b) := by
  have htotal : physicalWindowMass steps 0 A=∑b,physicalWindowMass steps 0 (J b) := by
    rw [←hcover,physicalWindowMass,Finset.sum_biUnion]
    · rfl
    · intro b _ c _ hbc
      exact hdisjoint hbc
  have hkept := native_kept_disjoint_mass steps J keep hdisjoint
  refine ⟨htotal,hkept,?_⟩
  rw [htotal,hkept,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

theorem native_height_bins_coordinate_mass {ι : Type} {K bins : ℕ}
    (steps : List (GaussianStep ι)) (S : Fin (steps.length+1)→ℝ)
    (A : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1)→Fin K)
    (w : ℝ) (hbins : 0<bins) (keep : Fin bins→Bool)
    (r : Fin (steps.length+1)→ℝ) (U : Set ℝ)
    (C : ∀b:Fin bins,NativeConstructedCoordinates steps
      (NativeUnitHeight.bin S A unit bins w b) r U) :
    physicalWindowMass steps 0 A=∑b,(C b).x (C b).K ∧
    physicalWindowMass steps 0 (nativeKeptRows (NativeUnitHeight.bin S A unit bins w) keep)=
      (∑b,if keep b then (C b).x (C b).K else 0) ∧
    physicalWindowMass steps 0 A-
      physicalWindowMass steps 0 (nativeKeptRows (NativeUnitHeight.bin S A unit bins w) keep)=
      ∑b,if keep b then 0 else (C b).x (C b).K := by
  have hh := native_height_bins_mass_accounting steps A (NativeUnitHeight.bin S A unit bins w) keep
    (native_height_bins_disjoint S A unit w) (native_height_bins_union S A unit w hbins)
  simpa only [(C _).width] using hh

theorem native_height_bins_discarded_mass_le {ι : Type} {K bins : ℕ}
    (steps : List (GaussianStep ι)) (S : Fin (steps.length+1)→ℝ)
    (A : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1)→Fin K)
    (w : ℝ) (hbins : 0<bins) (keep : Fin bins→Bool)
    (r : Fin (steps.length+1)→ℝ) (U : Set ℝ)
    (C : ∀b:Fin bins,NativeConstructedCoordinates steps
      (NativeUnitHeight.bin S A unit bins w b) r U)
    {delta : ℝ} (hdelta : 0≤delta)
    (hkeep : ∀b,keep b=false→(C b).x (C b).K<2*delta) :
    physicalWindowMass steps 0 A-
      physicalWindowMass steps 0 (nativeKeptRows (NativeUnitHeight.bin S A unit bins w) keep)≤
        2*(bins:ℝ)*delta := by
  rw [(native_height_bins_coordinate_mass steps S A unit w hbins keep r U C).2.2]
  calc
    _ ≤ ∑_b:Fin bins,2*delta := by
      apply Finset.sum_le_sum
      intro b _
      cases hb : keep b
      · simpa only [hb,Bool.false_eq_true,ite_false] using (hkeep b hb).le
      · simp only [ite_true]
        positivity
    _ = 2*(bins:ℝ)*delta := by simp;ring

end OAI.SKFluctuations.LaplaceWindowFormalization
