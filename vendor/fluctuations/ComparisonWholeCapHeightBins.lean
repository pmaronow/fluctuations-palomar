module

public import ComparisonCapHeightEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def heightBin (k : ℕ) (w h : ℝ) : ℕ := min ⌊h/w⌋₊ (k-1)

theorem heightBin_lt {k : ℕ} (hk : 0<k) (w h : ℝ) : heightBin k w h<k := by
  unfold heightBin
  exact (min_le_right _ _).trans_lt (by omega)

theorem heightBin_monotone {k : ℕ} {w : ℝ} (hw : 0<w) : Monotone (heightBin k w) := by
  intro h t hht
  exact min_le_min_right (k-1) (Nat.floor_mono (div_le_div_of_nonneg_right hht hw.le))

theorem heightBin_bounds {k : ℕ} {w h : ℝ} (hk : 0<k) (hw : 0<w)
    (hh : h∈Icc (0:ℝ) ((k:ℝ)*w)) :
    (heightBin k w h:ℝ)*w ≤ h ∧ h ≤ ((heightBin k w h:ℝ)+1)*w := by
  have hdiv : 0≤h/w := div_nonneg hh.1 hw.le
  have hfloor := Nat.floor_le hdiv
  have hbinfloor : (heightBin k w h:ℝ)≤(⌊h/w⌋₊:ℝ) := by
    exact_mod_cast (min_le_left ⌊h/w⌋₊ (k-1))
  refine ⟨(le_div_iff₀ hw).mp (hbinfloor.trans hfloor),?_⟩
  by_cases hf:⌊h/w⌋₊<k
  · have he : heightBin k w h=⌊h/w⌋₊ := min_eq_left (by omega)
    rw [he]
    exact ((div_lt_iff₀ hw).mp (Nat.lt_floor_add_one (h/w))).le
  · have he : heightBin k w h=k-1 := min_eq_right (by omega)
    rw [he]
    have hc : ((k-1:ℕ):ℝ)+1=(k:ℝ) := by
      exact_mod_cast (show k-1+1=k by omega)
    rw [hc]
    exact hh.2

theorem sameHeightBin_abs_le {k : ℕ} {w h t : ℝ} (hk : 0<k) (hw : 0<w)
    (hh : h∈Icc (0:ℝ) ((k:ℝ)*w)) (ht : t∈Icc (0:ℝ) ((k:ℝ)*w))
    (he : heightBin k w h=heightBin k w t) : |h-t|≤w := by
  have hb := heightBin_bounds hk hw hh
  have hc := heightBin_bounds hk hw ht
  rw [←he] at hc
  apply abs_le.mpr
  constructor <;> linarith

def heightBinSet (label : ℝ→ℝ) (a b : ℝ) (k : ℕ) (w : ℝ) (j : ℕ) : Set ℝ :=
  Icc a b∩{r | heightBin k w (label r)=j}

theorem heightBinSet_ordConnected {label : ℝ→ℝ} {a b w : ℝ} {k : ℕ}
    (hm : MonotoneOn label (Icc a b)) (hw : 0<w) (j : ℕ) :
    OrdConnected (heightBinSet label a b k w j) := by
  constructor
  intro r hr t ht z hz
  have hzi : z∈Icc a b := ⟨hr.1.1.trans hz.1,hz.2.trans ht.1.2⟩
  refine ⟨hzi,?_⟩
  have hleft := heightBin_monotone (k:=k) hw (hm hr.1 hzi hz.1)
  have hright := heightBin_monotone (k:=k) hw (hm hzi ht.1 hz.2)
  rw [hr.2] at hleft
  rw [ht.2] at hright
  exact le_antisymm hright hleft

theorem heightBinSet_measurableSet {label : ℝ→ℝ} {a b w : ℝ} {k : ℕ}
    (hm : MonotoneOn label (Icc a b)) (hw : 0<w) (j : ℕ) :
    MeasurableSet (heightBinSet label a b k w j) :=
  (heightBinSet_ordConnected hm hw j).measurableSet

theorem heightBinSet_partition {label : ℝ→ℝ} {a b w : ℝ} {k : ℕ}
    (hk : 0<k) : (⋃j∈Finset.range k,heightBinSet label a b k w j)=Icc a b := by
  ext r
  constructor
  · intro hr
    obtain ⟨j,hj,hrj⟩ := mem_iUnion₂.mp hr
    exact hrj.1
  · intro hr
    exact mem_iUnion₂.mpr ⟨heightBin k w (label r),
      Finset.mem_range.mpr (heightBin_lt hk w (label r)),hr,rfl⟩

theorem heightBinSet_disjoint (label : ℝ→ℝ) (a b : ℝ) (k : ℕ) (w : ℝ)
    {i j : ℕ} (hij : i≠j) : Disjoint (heightBinSet label a b k w i)
      (heightBinSet label a b k w j) := by
  apply disjoint_left.mpr
  intro r hr ht
  exact hij (hr.2.symm.trans ht.2)

theorem heightBinSet_ordered {label : ℝ→ℝ} {a b w : ℝ} {k i j : ℕ}
    (hm : MonotoneOn label (Icc a b)) (hw : 0<w) (hij : i<j)
    {r t : ℝ} (hr : r∈heightBinSet label a b k w i)
    (ht : t∈heightBinSet label a b k w j) : r≤t := by
  by_contra hno
  have hmono := heightBin_monotone (k:=k) hw (hm ht.1 hr.1 (lt_of_not_ge hno).le)
  rw [ht.2,hr.2] at hmono
  omega

def capHeightBin (U : Set ℝ) (S : ℝ→ℝ) (k : ℕ) (w : ℝ) (r : ℝ) : ℕ :=
  heightBin k w (capEndHeight U S r)

theorem capHeightBin_const_on_component (U : Set ℝ) (S : ℝ→ℝ) (k : ℕ) (w : ℝ)
    {r t : ℝ} (hr : r∈U) (ht : t∈ordConnectedComponent U r) :
    capHeightBin U S k w t=capHeightBin U S k w r := by
  unfold capHeightBin
  rw [capEndHeight_const_on_component U S hr ht]

theorem capHeightBinSet_contains_whole_component {U : Set ℝ} {S : ℝ→ℝ}
    {a b w : ℝ} {k : ℕ} (hU : U⊆Icc a b) {r : ℝ} (hr : r∈U) :
    ordConnectedComponent U r ⊆ heightBinSet (capEndHeight U S) a b k w
      (capHeightBin U S k w r) := by
  intro t ht
  exact ⟨hU (ordConnectedComponent_subset ht),capHeightBin_const_on_component U S k w hr ht⟩

theorem sameCapHeightBin_overlap_abs_le {U : Set ℝ} {S : ℝ→ℝ}
    {a b w L : ℝ} {k : ℕ} (hk : 0<k) (hw : 0<w) (hL : 0≤L)
    (hU : U⊆Icc a b) (hSb : ∀r∈Icc a b,S r∈Icc (0:ℝ) ((k:ℝ)*w))
    (hcap : ∀r∈U,∀t∈ordConnectedComponent U r,S t≤S r+L)
    {r t : ℝ} (hr : r∈Icc a b) (ht : t∈Icc a b)
    (he : capHeightBin U S k w r=capHeightBin U S k w t) : |S r-S t|≤w+L := by
  have hrb := capEndHeight_bounds hU (fun r hr=>(hSb r hr).2) hr
  have htb := capEndHeight_bounds hU (fun r hr=>(hSb r hr).2) ht
  have hrl := capEndHeight_sub_le hU (fun r hr=>(hSb r hr).2) hL hcap hr
  have htl := capEndHeight_sub_le hU (fun r hr=>(hSb r hr).2) hL hcap ht
  have hosc := sameHeightBin_abs_le hk hw
    ⟨(hSb r hr).1.trans hrb.1,hrb.2⟩ ⟨(hSb t ht).1.trans htb.1,htb.2⟩ he
  rcases abs_le.mp hosc with ⟨hleft,hright⟩
  apply abs_le.mpr
  constructor <;> linarith

def effectiveBinEdges (x : ℕ→ℝ) (δ : ℝ) (j : ℕ) : Set ℝ :=
  Ico (x j) (min (x (j+1)) (x j+δ)) ∪
    Ico (max (x j) (x (j+1)-δ)) (x (j+1))

theorem effectiveBinEdges_measurableSet (x : ℕ→ℝ) (δ : ℝ) (j : ℕ) :
    MeasurableSet (effectiveBinEdges x δ j) := measurableSet_Ico.union measurableSet_Ico

theorem effectiveBinEdges_mass_le (x : ℕ→ℝ) {δ : ℝ} (hδ : 0≤δ) (j : ℕ) :
    volume.real (effectiveBinEdges x δ j) ≤ 2*δ := by
  have hleft : volume.real (Ico (x j) (min (x (j+1)) (x j+δ))) ≤ δ := by
    rw [Real.volume_real_Ico]
    apply max_le
    · linarith [min_le_right (x (j+1)) (x j+δ)]
    · exact hδ
  have hright : volume.real (Ico (max (x j) (x (j+1)-δ)) (x (j+1))) ≤ δ := by
    rw [Real.volume_real_Ico]
    apply max_le
    · linarith [le_max_right (x j) (x (j+1)-δ)]
    · exact hδ
  exact (measureReal_union_le _ _).trans (by linarith)

theorem effectiveBinEdges_total_mass_le (x : ℕ→ℝ) (k : ℕ) {δ : ℝ} (hδ : 0≤δ) :
    volume.real (⋃j∈Finset.range k,effectiveBinEdges x δ j) ≤ 2*(k:ℝ)*δ := by
  calc
    _ ≤ ∑j∈Finset.range k,volume.real (effectiveBinEdges x δ j) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑j∈Finset.range k,2*δ := Finset.sum_le_sum (fun j _=>effectiveBinEdges_mass_le x hδ j)
    _ = _ := by simp; ring

end OAI.SKFluctuations.WholeUnitSideKernel
