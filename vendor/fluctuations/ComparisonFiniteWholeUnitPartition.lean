module

public import ComparisonSelectedUnitSampling
public import ComparisonCapContactUnits
public import ComparisonWholeCapHeightBins
public import ComparisonWholeCapDecomposition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set MeasureTheory Hierarchy
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def firstWholeUnitCell {N : ℕ} (U : Set ℝ) (r : Fin N → ℝ) (i : Fin N) : Fin N :=
  (Finset.univ.filter (fun j =>  wholeUnit U (r j)=wholeUnit U (r i))).min'
    ⟨i,by simp⟩

theorem firstWholeUnitCell_spec {N : ℕ} (U : Set ℝ) (r : Fin N → ℝ) (i : Fin N) :
    wholeUnit U (r (firstWholeUnitCell U r i))=wholeUnit U (r i) ∧
      firstWholeUnitCell U r i ≤ i := by
  constructor
  · unfold firstWholeUnitCell
    exact (Finset.mem_filter.mp (Finset.min'_mem
      (Finset.univ.filter (fun j:Fin N => wholeUnit U (r j)=wholeUnit U (r i))) _)).2
  · exact Finset.min'_le _ _ (by simp)

theorem firstWholeUnitCell_eq_iff {N : ℕ} (U : Set ℝ) (r : Fin N → ℝ) (i j : Fin N) :
    firstWholeUnitCell U r i=firstWholeUnitCell U r j ↔ wholeUnit U (r i)=wholeUnit U (r j) := by
  constructor
  · intro h
    exact (firstWholeUnitCell_spec U r i).1.symm.trans
      (h ▸ (firstWholeUnitCell_spec U r j).1)
  · intro h
    unfold firstWholeUnitCell
    congr 1
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [h]

theorem firstWholeUnitCell_monotone {N : ℕ} (U : Set ℝ) (r : Fin N → ℝ)
    (hr : Monotone r) : Monotone (firstWholeUnitCell U r) := by
  intro i j hij
  by_contra hno
  have hlt : firstWholeUnitCell U r j < firstWholeUnitCell U r i := lt_of_not_ge hno
  have hmi : firstWholeUnitCell U r j ≤ i := hlt.le.trans (firstWholeUnitCell_spec U r i).2
  have hunit : r i∈wholeUnit U (r j) := by
    apply (wholeUnit_ordConnected U (r j)).out'
      ((firstWholeUnitCell_spec U r j).1 ▸ self_mem_wholeUnit U (r (firstWholeUnitCell U r j)))
      (self_mem_wholeUnit U (r j))
    exact ⟨hr hmi,hr hij⟩
  have he := (firstWholeUnitCell_eq_iff U r i j).mpr (wholeUnit_eq_of_mem U hunit)
  exact (ne_of_lt hlt) he.symm

def positiveSelectedCells {ι : Type} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) : Finset (Fin (steps.length+1)) :=
  J.filter (fun i =>  0 < pathMassDifferences steps 0 i)

theorem positiveSelectedCells_mass {ι : Type} (steps : List (GaussianStep ι))
    (ha : OrderedSteps 0 steps) (J : Finset (Fin (steps.length+1))) :
    physicalWindowMass steps 0 (positiveSelectedCells steps J)=physicalWindowMass steps 0 J := by
  unfold physicalWindowMass positiveSelectedCells
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : 0 < pathMassDifferences steps 0 i
  · simp [hp]
  · have hz : pathMassDifferences steps 0 i=0 := le_antisymm (le_of_not_gt hp)
      (pathMassDifferences_nonneg steps ha i)
    simp [hp,hz]

theorem exists_finite_selected_unit_coordinates {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (J : Finset (Fin (steps.length+1))) (hJ : J.Nonempty)
    (hp : ∀i∈J,0 < pathMassDifferences steps 0 i)
    (rep : Fin (steps.length+1) → Fin (steps.length+1))
    (hm : MonotoneOn rep (J:Set (Fin (steps.length+1)))) :
    ∃ (K : ℕ) (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ),
      0 < K ∧ x 0=0 ∧ x K=physicalWindowMass steps 0 J ∧
      (∀u:Fin K,x u.val < x (u.val+1)) ∧
      (∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val) ∧
      (∀i∈J,∀j∈J,unit i=unit j ↔ rep i=rep j) ∧
      MonotoneOn unit (J:Set (Fin (steps.length+1))) := by
  let T := J.image rep
  have hT : T.Nonempty := hJ.image rep
  have hK : 0 < T.card := Finset.card_pos.mpr hT
  let e := T.orderIsoOfFin rfl
  let unit : Fin (steps.length+1) → Fin T.card := fun i => 
    if hi:i∈J then e.symm ⟨rep i,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩ else ⟨0,hK⟩
  have hu (i : Fin (steps.length+1)) (hi:i∈J) :
      e (unit i)=⟨rep i,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩ := by
    simp only [unit,dite_eq_left hi,e.apply_symm_apply]
  have hclass (i : Fin (steps.length+1)) (hi:i∈J) (j : Fin (steps.length+1)) (hj:j∈J) :
      unit i=unit j ↔ rep i=rep j := by
    constructor
    · intro he
      exact congrArg Subtype.val ((hu i hi).symm.trans ((congrArg e he).trans (hu j hj)))
    · intro he
      apply e.injective
      rw [hu i hi,hu j hj]
      exact Subtype.ext he
  have hunit : MonotoneOn unit (J:Set (Fin (steps.length+1))) := by
    intro i hi j hj hij
    apply e.le_iff_le.mp
    rw [hu i hi,hu j hj]
    exact hm hi hj hij
  let mass := fun u =>  physicalSelectedUnitMass steps J unit u
  have hmass : ∀u,0 < mass u := by
    intro u
    obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp (e u).property
    have hui : unit i=u := by
      apply e.injective
      rw [hu i hi]
      exact Subtype.ext hei
    unfold mass physicalSelectedUnitMass
    refine Finset.sum_pos' ?_ ?_
    · intro k hk
      split_ifs
      · exact pathMassDifferences_nonneg steps ha _
      · exact le_rfl
    · refine ⟨i,Finset.mem_univ i,?_⟩
      simp only [hi,hui,and_self,ite_true]
      exact hp i hi
  let x : ℕ → ℝ := fun k =>  ∑u:Fin T.card,if u.val < k then mass u else 0
  have hx0 : x 0=0 := by simp [x]
  have hdiff (u : Fin T.card) : x (u.val+1)-x u.val=mass u := by
    have he (v : Fin T.card) :
        (if v.val < u.val+1 then mass v else 0)-(if v.val < u.val then mass v else 0)=
          if v=u then mass u else 0 := by
      by_cases hv:v=u
      · subst v; simp
      · have hvv:v.val≠u.val := fun hh =>  hv (Fin.ext hh)
        by_cases hlt:v.val < u.val  <;>  simp [hv,hlt,show (v.val < u.val+1) ↔ v.val < u.val by omega]
    change (∑v:Fin T.card,if v.val < u.val+1 then mass v else 0)-
      (∑v:Fin T.card,if v.val < u.val then mass v else 0)=mass u
    rw [←Finset.sum_sub_distrib]
    simp_rw [he]
    simp
  have hxK : x T.card=physicalWindowMass steps 0 J := by
    simp only [x,Fin.is_lt,ite_true]
    have hg := selected_mass_grouping steps J unit (fun _ =>  1)
    simpa only [mass,mul_ite,mul_one,mul_zero,physicalWindowMass,Finset.sum_ite_mem,
      Finset.univ_inter] using hg.symm
  refine ⟨T.card,unit,x,hK,hx0,hxK,?_,?_,hclass,hunit⟩
  · intro u
    exact sub_pos.mp (hdiff u ▸ hmass u)
  · intro u
    exact (hdiff u).symm

def selectedWholeUnitBinCells {ι : Type} (steps : List (GaussianStep ι))
    (r : Fin (steps.length+1) → ℝ) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ)
    (a b : ℝ) (k : ℕ) (w : ℝ) (j : ℕ) : Finset (Fin (steps.length+1)) :=
  Finset.univ.filter (fun i => 0 < pathMassDifferences steps 0 i ∧
    r i∈wholeCapRetainedRegion a b U F ∧ capHeightBin U S k w (r i)=j)

@[simp] theorem mem_selectedWholeUnitBinCells {ι : Type}
    (steps : List (GaussianStep ι)) (r : Fin (steps.length+1) → ℝ)
    (U : Set ℝ) (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ)
    (a b : ℝ) (k : ℕ) (w : ℝ) (j : ℕ) (i : Fin (steps.length+1)) :
    i∈selectedWholeUnitBinCells steps r U F S a b k w j ↔
      0 < pathMassDifferences steps 0 i ∧ r i∈wholeCapRetainedRegion a b U F ∧
        capHeightBin U S k w (r i)=j := by simp [selectedWholeUnitBinCells]

theorem wholeCapRetainedRegion_wholeUnit_closed {U : Set ℝ} {a b r t : ℝ}
    (hU : U⊆Icc a b) (F : Finset (ordConnectedSection U))
    (hr : r∈wholeCapRetainedRegion a b U F) (ht : t∈wholeUnit U r) :
    t∈wholeCapRetainedRegion a b U F := by
  by_cases hrU:r∈U
  · have htC : t∈ordConnectedComponent U r := by simpa [wholeUnit,hrU] using ht
    rcases hr with hr|hr
    · exact False.elim (hr.2 hrU)
    · obtain ⟨z,hz,hrz⟩ := mem_iUnion₂.mp hr
      have he : ordConnectedComponent U r=ordConnectedComponent U z.val :=
        (ordConnectedComponent_eq hrz).symm
      exact Or.inr (mem_iUnion₂.mpr ⟨z,hz,he ▸ htC⟩)
  · have he : t=r := by simpa [wholeUnit,hrU] using ht
    exact he ▸ hr

theorem selectedWholeUnitBinCells_complete {ι : Type}
    (steps : List (GaussianStep ι)) (r : Fin (steps.length+1) → ℝ)
    {U : Set ℝ} {a b : ℝ} (hU : U⊆Icc a b)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ)
    (k : ℕ) (w : ℝ) (j : ℕ) {i t : Fin (steps.length+1)}
    (hi : i∈selectedWholeUnitBinCells steps r U F S a b k w j)
    (hp : 0 < pathMassDifferences steps 0 t)
    (ht : r t∈wholeUnit U (r i)) :
    t∈selectedWholeUnitBinCells steps r U F S a b k w j := by
  obtain ⟨_,hr,hbin⟩ := (mem_selectedWholeUnitBinCells _ _ _ _ _ _ _ _ _ _ _).mp hi
  apply (mem_selectedWholeUnitBinCells _ _ _ _ _ _ _ _ _ _ _).mpr
  refine ⟨hp,wholeCapRetainedRegion_wholeUnit_closed hU F hr ht,?_⟩
  unfold capHeightBin at hbin ⊢
  rw [capEndHeight_const_on_wholeUnit U S ht]
  exact hbin

theorem selectedWholeUnitBin_exists_coordinates {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (r : Fin (steps.length+1) → ℝ) (hr : Monotone r) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ)
    (a b : ℝ) (k : ℕ) (w : ℝ) (j : ℕ)
    (hJ : (selectedWholeUnitBinCells steps r U F S a b k w j).Nonempty) :
    let J := selectedWholeUnitBinCells steps r U F S a b k w j
    ∃ (K : ℕ) (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ),
      0 < K ∧ x 0=0 ∧ x K=physicalWindowMass steps 0 J ∧
      (∀u:Fin K,x u.val < x (u.val+1)) ∧
      (∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val) ∧
      (∀i∈J,∀t∈J,unit i=unit t ↔ wholeUnit U (r i)=wholeUnit U (r t)) ∧
      MonotoneOn unit (J:Set (Fin (steps.length+1))) := by
  dsimp only
  obtain ⟨K,unit,x,hK,h0,hend,hx,hmass,hclass,horder⟩ :=
    exists_finite_selected_unit_coordinates steps ha _ hJ
      (fun i hi => ((mem_selectedWholeUnitBinCells _ _ _ _ _ _ _ _ _ _ _).mp hi).1)
      (firstWholeUnitCell U r) ((firstWholeUnitCell_monotone U r hr).monotoneOn _)
  refine ⟨K,unit,x,hK,h0,hend,hx,hmass,?_,horder⟩
  intro i hi t ht
  exact (hclass i hi t ht).trans (firstWholeUnitCell_eq_iff U r i t)

theorem selectedWholeUnitBinCells_contact_retained {ι : Type}
    (steps : List (GaussianStep ι)) (r : Fin (steps.length+1) → ℝ)
    (U : Set ℝ) (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ)
    {a b : ℝ} (k : ℕ) (w : ℝ) (i : Fin (steps.length+1))
    (hp : 0 < pathMassDifferences steps 0 i) (hr : r i∈Icc a b) (hc : r i∉U) :
    i∈selectedWholeUnitBinCells steps r U F S a b k w (capHeightBin U S k w (r i)) := by
  apply (mem_selectedWholeUnitBinCells _ _ _ _ _ _ _ _ _ _ _).mpr
  exact ⟨hp,Or.inl ⟨hr,hc⟩,rfl⟩

def retainedWholeUnitCells {ι : Type} (steps : List (GaussianStep ι))
    (r : Fin (steps.length+1) → ℝ) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) (a b : ℝ) : Finset (Fin (steps.length+1)) :=
  Finset.univ.filter (fun i => r i∈wholeCapRetainedRegion a b U F)

theorem selectedWholeUnitBinCells_total_mass {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (r : Fin (steps.length+1) → ℝ) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ)
    (a b : ℝ) {k : ℕ} (hk : 0 < k) (w : ℝ) :
    (∑j∈Finset.range k,physicalWindowMass steps 0
      (selectedWholeUnitBinCells steps r U F S a b k w j))=
      physicalWindowMass steps 0 (retainedWholeUnitCells steps r U F a b) := by
  unfold physicalWindowMass selectedWholeUnitBinCells retainedWholeUnitCells
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : 0 < pathMassDifferences steps 0 i
  · by_cases hr : r i∈wholeCapRetainedRegion a b U F
    · simp only [hp,hr,true_and,ite_true]
      rw [Finset.sum_eq_single (capHeightBin U S k w (r i))]
      · simp
      · intro j hj hne
        simp only [Ne.symm hne,ite_false]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (heightBin_lt hk w _)))
    · simp [hr]
  · have hz : pathMassDifferences steps 0 i=0 := le_antisymm (le_of_not_gt hp)
      (pathMassDifferences_nonneg steps ha i)
    simp [hz]

theorem retainedWholeUnitCells_add_omitted_mass {ι : Type}
    (steps : List (GaussianStep ι)) (r : Fin (steps.length+1) → ℝ)
    (U : Set ℝ) (F : Finset (ordConnectedSection U)) (a b : ℝ) :
    let J := retainedWholeUnitCells steps r U F a b
    physicalWindowMass steps 0 J+physicalWindowMass steps 0 (Finset.univ\J)=1 := by
  dsimp only
  unfold physicalWindowMass
  rw [←Finset.compl_eq_univ_sdiff,Finset.sum_add_sum_compl]
  simpa using sum_pathMassDifferences steps (0:ℝ)

theorem selectedWholeUnitBinCells_weighted_decomposition {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (r : Fin (steps.length+1) → ℝ) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ)
    (a b : ℝ) {k : ℕ} (hk : 0 < k) (w : ℝ)
    (obs : Fin (steps.length+1) → ℝ) :
    (∑j∈Finset.range k,∑i∈selectedWholeUnitBinCells steps r U F S a b k w j,
      pathMassDifferences steps 0 i*obs i)=
      ∑i∈retainedWholeUnitCells steps r U F a b,pathMassDifferences steps 0 i*obs i := by
  unfold selectedWholeUnitBinCells retainedWholeUnitCells
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : 0 < pathMassDifferences steps 0 i
  · by_cases hr : r i∈wholeCapRetainedRegion a b U F
    · simp only [hp,hr,true_and,ite_true]
      rw [Finset.sum_eq_single (capHeightBin U S k w (r i))]
      · simp
      · intro j hj hne
        simp only [Ne.symm hne,ite_false]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (heightBin_lt hk w _)))
    · simp [hr]
  · have hz : pathMassDifferences steps 0 i=0 := le_antisymm (le_of_not_gt hp)
      (pathMassDifferences_nonneg steps ha i)
    simp [hz]

theorem retainedWholeUnitCells_weighted_add_omitted {ι : Type}
    (steps : List (GaussianStep ι)) (r : Fin (steps.length+1) → ℝ)
    (U : Set ℝ) (F : Finset (ordConnectedSection U)) (a b : ℝ)
    (obs : Fin (steps.length+1) → ℝ) :
    let J := retainedWholeUnitCells steps r U F a b
    (∑i∈J,pathMassDifferences steps 0 i*obs i)+
      (∑i∈Finset.univ\J,pathMassDifferences steps 0 i*obs i)=
      ∑i,pathMassDifferences steps 0 i*obs i := by
  dsimp only
  rw [←Finset.compl_eq_univ_sdiff,Finset.sum_add_sum_compl]

end OAI.SKFluctuations.WholeUnitSideKernel

