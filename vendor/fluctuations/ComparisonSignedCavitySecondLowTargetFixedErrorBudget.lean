module

public import ComparisonSignedCavitySecondLowSoleRootTargetCutSource
public import ComparisonSignedCavitySecondLowEntryFourBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_second_low_sole_root_target_fixed_error_budget
    (Bclock Temp Cf Couter : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ) (x : ℝ) (hU : U≤as.length),i<U → M.xs≤x → x≤M.canonicalDirectTestBandScale →
          partitionPoint 0 as U≤Couter*x →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        ∀(j : Fin 8) (firstError : Bool),
          |nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K g.tree hU (fun _=>1)
            (g.embed (singleSlot as)) g.mark j firstError/2|≤
            C*x^2*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_sole_root_target_cut_error_words
    (D:=D) Bclock Temp Cf Couter hTemp hCf hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨480*(1+Couter)*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M HS hxs L us hus hret hmesh
  filter_upwards [hn M HS hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i U x hU hi hxsx hxW houter j firstError
  let as:=finiteCutMasses us k
  let b:=fun l=>(M.bf (partitionPoint 0 as l):ℝ)
  let h:=fun l=>(M.hf (partitionPoint 0 as l):ℝ)
  let K:=fun l=>h l+b l*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as l)
  let q : ℕ→RestCoordinate n→ℝ:=fun l=>Sum.elim (fun _=>b l) (fun _=>h l)
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let F:=nativeSecondLowFixedErrorUnobservedWord n q i U b h K hU (fun _=>1)
    (g.embed (singleSlot as)) g.mark j firstError
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let Drow:=C*x*Cerr*di
  have hx : 0<x:=M.hxs.trans_le hxsx
  have hdi : 0≤di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hCerr : 0≤Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hDrow : 0≤Drow:=by dsimp [Drow];positivity
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have Hleaves : g.tree.leaves≤2:=by
    have HL:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ 0 _ i)
    simpa only [single_leaves_exact] using HL
  have HF : ∀p∈g.tree.markedAttach 0,∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,|F p r s t|≤Drow := by
    intro p hp r hr s hs t ht
    dsimp only [F,nativeSecondLowFixedErrorUnobservedWord,nativeSecondLowUnobservedErrorWord]
    split_ifs with Hindex _Hpath
    · by_cases Hfirst : r.tree.splitIndex (r.embed p.mark) r.mark<U
      · by_cases Hsecond : t.tree.splitIndex (t.embed s.mark) t.mark<U
        · have HB:=hk i U x hU hi hxsx hxW houter p hp r hr s hs t ht Hfirst Hsecond
          cases firstError
          · simp only [nativeSecondLowErrorCut,Bool.false_eq_true,ite_false] at Hindex
            rw [Hindex] at HB
            exact HB.2
          · simp only [nativeSecondLowErrorCut,ite_true] at Hindex
            rw [Hindex] at HB
            exact HB.1
        · rw [native_second_low_error_word_zero_second_high n q U b h K (fun _=>1)
            (g.embed (singleSlot as)) g.mark firstError p r s t (not_lt.mp Hsecond)]
          simpa only [abs_zero] using hDrow
      · rw [native_second_low_error_word_zero_first_high n q U b h K (fun _=>1)
          (g.embed (singleSlot as)) g.mark firstError p r s hs t ht (not_lt.mp Hfirst)]
        simpa only [abs_zero] using hDrow
    · simpa only [abs_zero] using hDrow
    · simpa only [abs_zero] using hDrow
  have HE:=native_second_low_entry_four_average_abs_le g.tree U hU ho Hleaves
    (nativeSecondLowFirstMiddleIsFirst j) F hDrow HF
  rw [←native_second_low_fixed_error_unobserved_class_eq_entry n q i U b h K g.tree hU (fun _=>1)
    (g.embed (singleSlot as)) g.mark j firstError] at HE
  have Hpos : 0≤480*partitionPoint 0 as U*Drow:=by
    have HM:=(partitionPoint_mem as ho U).1
    positivity
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _≤(480*partitionPoint 0 as U*Drow)/2:=by
      have HH:=div_le_div_of_nonneg_right HE (by norm_num : (0:ℝ)≤2)
      norm_num only [Nat.cast_ofNat] at HH
      convert HH using 1
    _≤480*partitionPoint 0 as U*Drow:=by nlinarith
    _≤480*(Couter*x)*Drow:=by gcongr
    _≤480*((1+Couter)*x)*Drow:=by gcongr;linarith
    _=_:=by dsimp [Drow,di,Cerr];ring

end OAI.SKFluctuations.Cavity
