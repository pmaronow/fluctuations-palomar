module

public import ComparisonSignedCavityActualGammaHighPolarization

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

def nativeRestProjectedPairedTest {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (τ : p.tree.cavityLeft.Assignment) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  (A (p.restSpin τ) (g.restSpin (p.restRestrict τ))-
    A (T.cavityLeft.atSlot (g.restRestrict (p.restRestrict τ)) (T.cavityLeftSlot s))
      (g.restSpin (p.restRestrict τ)))*
    (P (g.restRestrict (p.restRestrict τ))-
      P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
        (g.restRestrict (p.restRestrict τ)) (p.restSpin τ)))

theorem native_rest_projected_paired_constant_zero {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (A : Spin n→Spin n→ℝ) (c : ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree) :
    nativeRestProjectedPairedTest T s star A (fun _=>c) p=fun _=>0 := by
  funext τ
  simp only [nativeRestProjectedPairedTest,sub_self,mul_zero]

theorem native_rest_projected_paired_test_actual {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree) (σ : p.tree.Assignment) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeRestProjectedPairedTest T s star A P p (p.tree.cavityAssignment σ).1=
      (A (p.spin σ).1 (g.spin (p.restrict σ)).1-
        A (T.atSlot (g.restrict (p.restrict σ)) s).1 (g.spin (p.restrict σ)).1)*
        (P (T.cavityAssignment (g.restrict (p.restrict σ))).1-
          P (T.cavityAssignment (nativeReplaceAtSlot T s
            (g.restrict (p.restrict σ)) (p.spin σ))).1) := by
  dsimp only [nativeRestProjectedPairedTest]
  rw [←p.restSpin_actual,←p.restRestrict_actual,
    ←(nativeFreshAtSlot T 0 s star).restSpin_actual,
    ←(nativeFreshAtSlot T 0 s star).restRestrict_actual,T.atSlot_cavityLeft,
    native_replace_cavityLeft_actual]

theorem native_actual_generated_first_high_rest_polarization
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 P₀.live.test.target star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 P₀.live.test.target star).tree.markedAttach 0)
    (hpH : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j j₀,0 ≤ q j j₀) (hq : ∀j₀,Monotone (fun j=>q j j₀))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
      (nativeRestProjectedDisplacementTest T P₀.live.test.target star A P p) []=
      (1/2:ℝ)*retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
        (nativeRestProjectedPairedTest T P₀.live.test.target star A P p) [] := by
  have H0:=actual_frozen_coefficient_eq_retained n q U b h K p.tree ho
    (nativeRestProjectedDisplacementTest T P₀.live.test.target star A P p) []
    hq0 hq hb hh hK hbm hhm hKm 0 1
  have H1:=actual_frozen_coefficient_eq_retained n q U b h K p.tree ho
    (nativeRestProjectedPairedTest T P₀.live.test.target star A P p) []
    hq0 hq hb hh hK hbm hhm hKm 0 1
  simp only [siteMonomial,mul_one,List.replicate_zero,List.replicate_one,List.nil_append] at H0 H1
  rw [←H0,←H1]
  have HE:=native_actual_generated_fresh_high_jets_polarization hP hi hs ho q b h K p hp hpH
    (fun σ τ=>A σ.1 τ.1) (fun σ=>P (T.cavityAssignment σ).1)
    hq0 hq hb hh hK hbm hhm hKm 1 0 (by norm_num)
  simpa only [←native_rest_projected_displacement_test_actual,
    ←native_rest_projected_paired_test_actual] using HE

theorem native_actual_generated_Gamma_first_high_eq_paired_source
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j j₀,0 ≤ q j j₀) (hq : ∀j₀,Monotone (fun j=>q j j₀))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
    nativeGammaProjectedFirstHighDisplacement T P₀.live.test.target star U q b h K A P=
      (1/2:ℝ)*((g.tree.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed (g.embed P₀.live.test.target)) p.mark*
        retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
          (nativeRestProjectedPairedTest T P₀.live.test.target star A P p) [])).sum := by
  dsimp only
  unfold nativeGammaProjectedFirstHighDisplacement
  dsimp only
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hpH : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark
  · rw [native_actual_generated_first_high_rest_polarization hP hi hs ho q b h K p hp hpH
      A P hq0 hq hb hh hK hbm hhm hKm]
    ring
  · rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hP.highCut_le_length (lt_of_not_ge hpH)]
    ring

theorem native_actual_generated_Gamma_first_high_eq_three_signed_rows
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j j₀,0 ≤ q j j₀) (hq : ∀j₀,Monotone (fun j=>q j j₀))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
    nativeGammaProjectedFirstHighDisplacement T P₀.live.test.target star U q b h K A P=
      (1/4:ℝ)*((g.tree.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed (g.embed P₀.live.test.target)) p.mark*
        ((p.tree.markedAttach 0).map (fun r=>r.coeff*
          ((r.tree.markedAttach 0).map (fun z=>z.coeff*
            (z.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
              (insertedRestTest (nativeRestProjectedPairedTest T P₀.live.test.target star A P p)
                (restHighKernel n U b h K) r z) 0*
              fullScalarCutGamma z.tree U K (z.embed r.mark) z.mark))).sum)).sum)).sum := by
  dsimp only
  rw [native_actual_generated_Gamma_first_high_eq_paired_source hP hi hs ho q b h K A P
    hq0 hq hb hh hK hbm hhm hKm]
  simp_rw [native_retained_first_high_eq_signed_rest_Gamma_rows]
  rw [←List.sum_map_mul_left,←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  ring

end OAI.SKFluctuations.Cavity
