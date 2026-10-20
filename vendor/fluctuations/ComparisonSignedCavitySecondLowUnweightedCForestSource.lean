module

public import ComparisonSignedCavityCanonicalMarkedOldProduct
public import ComparisonSignedCavityActualRestBoundaryResampling
public import ComparisonSignedCavitySecondLowUnweightedCRowMass

@[expose] public section

noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

 theorem native_second_low_low_slots_ne {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (hU : U≤as.length)
    (f c : T.Slot) (hfc : T.splitIndex f c<U) : f≠c := by
  intro H
  rw [H,T.splitIndex_self] at hfc
  omega

 def nativeSecondLowTwoLowBoundaryShape (n : ℕ) (b h : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (f c z : T.Slot) (hfc : f≠c) (hzc : z≠c) : ActualNaturalBoundaryShape n 2 T where
  α:=fun e=>h (T.splitIndex (Fin.cases f (fun _=>z) e) c)
  β:=fun e=>b (T.splitIndex (Fin.cases f (fun _=>z) e) c)
  i:=Fin.cases f (fun _=>z)
  j:=fun _=>c
  distinct:=by intro e;exact Fin.cases hfc (fun _=>hzc) e
  lowInGrid:=fun e=>T.splitIndex_le_clockLength _ _

 private theorem unweighted_c_affine_rest_row (n U : ℕ) (b h : ℕ→ℝ)
    (i : ℕ) (hi : i<U) (σ τ : Spin n) :
    fullBoundaryAffineFactor n (h i) (b i) (σ,false) (τ,false)=restLowKernel n U b h i σ τ := by
  simp only [fullBoundaryAffineFactor,restLowKernel,hi,ite_true,deletedOverlap,joinSpin,Fin.lastCases_castSucc]

 private theorem unweighted_c_rest_row_symm (n U : ℕ) (b h : ℕ→ℝ)
    (i : ℕ) (σ τ : Spin n) : restLowKernel n U b h i σ τ=restLowKernel n U b h i τ σ := by
  simp only [restLowKernel,mul_comm]

 theorem native_second_low_two_LOW_forest_product
    (n U : ℕ) (b h : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (f c z : T.Slot)
    (hfc : f≠c) (hzc : z≠c) (Hfc : T.splitIndex f c<U) (Hcz : T.splitIndex c z<U)
    (σ : T.cavityLeft.Assignment) :
    (nativeSecondLowTwoLowBoundaryShape n b h T f c z hfc hzc).restProduct σ=
      restLowKernel n U b h (T.splitIndex f c)
        (T.cavityLeft.atSlot σ (T.cavityLeftSlot f)) (T.cavityLeft.atSlot σ (T.cavityLeftSlot c))*
      restLowKernel n U b h (T.splitIndex c z)
        (T.cavityLeft.atSlot σ (T.cavityLeftSlot c)) (T.cavityLeft.atSlot σ (T.cavityLeftSlot z)) := by
  unfold ActualNaturalBoundaryShape.restProduct
  rw [Fin.prod_univ_succ,Fin.prod_univ_one]
  change fullBoundaryAffineFactor n (h (T.splitIndex f c)) (b (T.splitIndex f c))
      (T.cavityLeft.atSlot σ (T.cavityLeftSlot c),false) (T.cavityLeft.atSlot σ (T.cavityLeftSlot f),false)*
    fullBoundaryAffineFactor n (h (T.splitIndex z c)) (b (T.splitIndex z c))
      (T.cavityLeft.atSlot σ (T.cavityLeftSlot c),false) (T.cavityLeft.atSlot σ (T.cavityLeftSlot z),false)=_
  rw [unweighted_c_affine_rest_row n U b h _ Hfc,
    T.splitIndex_symm z c,unweighted_c_affine_rest_row n U b h _ Hcz,
    unweighted_c_rest_row_symm n U b h (T.splitIndex f c)]

 theorem native_second_low_high_c_preserves_LOW {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (c f : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : U≤p.tree.splitIndex (p.embed c) p.mark) (hlow : T.splitIndex f c<U) :
    p.tree.splitIndex (p.embed f) p.mark=T.splitIndex f c := by
  have H:=p.tree.splitIndex_low_eq_of_high p.mark (p.embed c) (p.embed f) (U:=U)
    (by rw [p.tree.splitIndex_symm];exact hh)
    (by rw [(T.markedAttach_embed_preserves 0 p hp).2,T.splitIndex_symm];exact hlow)
  rw [p.tree.splitIndex_symm] at H
  exact H.trans (by rw [(T.markedAttach_embed_preserves 0 p hp).2,T.splitIndex_symm])

 theorem native_second_low_c_two_forest_same_low {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (c f z : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : U≤p.tree.splitIndex (p.embed c) p.mark)
    (hfc : T.splitIndex f c<U) (hzc : T.splitIndex z c<U) :
    ∀e : Fin 2,p.tree.splitIndex (Fin.cases (p.embed f) (fun _=>p.embed z) e) p.mark=
      p.tree.splitIndex (Fin.cases (p.embed f) (fun _=>p.embed z) e) (p.embed c) := by
  intro e
  refine Fin.cases ?_ (fun _=>?_) e
  · change p.tree.splitIndex (p.embed f) p.mark=p.tree.splitIndex (p.embed f) (p.embed c)
    rw [(T.markedAttach_embed_preserves 0 p hp).2]
    exact native_second_low_high_c_preserves_LOW T U c f p hp hh hfc
  · change p.tree.splitIndex (p.embed z) p.mark=p.tree.splitIndex (p.embed z) (p.embed c)
    rw [(T.markedAttach_embed_preserves 0 p hp).2]
    exact native_second_low_high_c_preserves_LOW T U c z p hp hh hzc

 def nativeSecondLowUnweightedCPayload (n U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (f c z : T.Slot) (P : T.cavityLeft.Assignment→ℝ)
    (p : MarkedPlacement T) (τ : p.tree.cavityLeft.Assignment) : ℝ :=
  P (p.restRestrict τ)*
    (restLowKernel n U b h (T.splitIndex f c)
      (T.cavityLeft.atSlot (p.restRestrict τ) (T.cavityLeftSlot f)) (p.restSpin τ)*
    restLowKernel n U b h (T.splitIndex c z) (p.restSpin τ)
      (T.cavityLeft.atSlot (p.restRestrict τ) (T.cavityLeftSlot z))-
    (if T.splitIndex f c<U then K (T.splitIndex f c) else 0)*
      (if T.splitIndex c z<U then K (T.splitIndex c z) else 0))

 def nativeSecondLowUnweightedCOldPayload (n U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (f c z : T.Slot) (P : T.cavityLeft.Assignment→ℝ) (τ : T.cavityLeft.Assignment) : ℝ :=
  P τ*(restLowKernel n U b h (T.splitIndex f c)
      (T.cavityLeft.atSlot τ (T.cavityLeftSlot f)) (T.cavityLeft.atSlot τ (T.cavityLeftSlot c))*
    restLowKernel n U b h (T.splitIndex c z)
      (T.cavityLeft.atSlot τ (T.cavityLeftSlot c)) (T.cavityLeft.atSlot τ (T.cavityLeftSlot z))-
    (if T.splitIndex f c<U then K (T.splitIndex f c) else 0)*
      (if T.splitIndex c z<U then K (T.splitIndex c z) else 0))

 theorem native_second_low_unweighted_c_two_factor_replacement
    (n U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (hU : U≤as.length) (f c z : T.Slot)
    (Hfc : T.splitIndex f c<U) (Hcz : T.splitIndex c z<U)
    (P : T.cavityLeft.Assignment→ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : U≤p.tree.splitIndex (p.embed c) p.mark) (τ : p.tree.cavityLeft.Assignment) :
    let Hf:=native_second_low_high_c_preserves_LOW T U c f p hp hh Hfc
    let Hz:=native_second_low_high_c_preserves_LOW T U c z p hp hh (by rwa [T.splitIndex_symm])
    let fn:=p.embed f
    let cn:=p.embed c
    let zn:=p.embed z
    let Hfn : fn≠p.mark:=native_second_low_low_slots_ne p.tree U hU fn p.mark (Hf.trans_lt Hfc)
    let Hzn : zn≠p.mark:=native_second_low_low_slots_ne p.tree U hU zn p.mark
      (Hz.trans_lt (by rwa [T.splitIndex_symm]))
    let G:=nativeSecondLowTwoLowBoundaryShape n b h p.tree fn p.mark zn Hfn Hzn
    let old:=G.retarget (fun _=>cn) (by
      intro e
      fin_cases e
      · exact fun H=>native_second_low_low_slots_ne T U hU f c Hfc ((T.markedAttach_embed_preserves 0 p hp).1 H)
      · exact fun H=>native_second_low_low_slots_ne T U hU z c (by rwa [T.splitIndex_symm])
          ((T.markedAttach_embed_preserves 0 p hp).1 H))
    nativeSecondLowUnweightedCPayload n U b h K T f c z P p τ-
      nativeSecondLowUnweightedCOldPayload n U b h K T f c z P (p.restRestrict τ)=
      P (p.restRestrict τ)*(G.restProduct τ-old.restProduct τ) := by
  dsimp only
  have Hf:=native_second_low_high_c_preserves_LOW T U c f p hp hh Hfc
  have Hz:=native_second_low_high_c_preserves_LOW T U c z p hp hh (by rwa [T.splitIndex_symm])
  simp only [nativeSecondLowUnweightedCPayload,nativeSecondLowUnweightedCOldPayload,
    ActualNaturalBoundaryShape.restProduct,ActualNaturalBoundaryShape.retarget,
    nativeSecondLowTwoLowBoundaryShape,Fin.prod_univ_succ,Fin.cases_zero,Fin.cases_succ,
    Hf,Hz,T.splitIndex_symm z c,←p.restRestrict_at,MarkedPlacement.restSpin]
  simp only [fullBoundaryAffineFactor,restLowKernel,Hfc,Hcz,ite_true,deletedOverlap,joinSpin,Fin.lastCases_castSucc]
  have Hsum (σ τ : Spin n) : (∑i,spinValue (σ i)*spinValue (τ i))=(∑i,spinValue (τ i)*spinValue (σ i)):=by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [Hsum (p.tree.cavityLeft.atSlot τ (p.tree.cavityLeftSlot p.mark))
      (T.cavityLeft.atSlot (p.restRestrict τ) (T.cavityLeftSlot f)),
    Hsum (T.cavityLeft.atSlot (p.restRestrict τ) (T.cavityLeftSlot c))
      (T.cavityLeft.atSlot (p.restRestrict τ) (T.cavityLeftSlot f))]
  ring

end OAI.SKFluctuations.Cavity
