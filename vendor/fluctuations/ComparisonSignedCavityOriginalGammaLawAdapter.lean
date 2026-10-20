module

public import ComparisonSignedCavityOriginalProjectedLawAdapter
public import ComparisonSignedCavityActualOriginalGammaLowOrientation
public import ComparisonSignedCavityLowGammaFullRestoration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000

theorem native_decoupled_gamma_weighted_rest_payload (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) :
    nativeOriginalGammaWeightedExpectation n 0 (cutFullVariance n q U 0 0 b h K) 0 U K T
      (fun σ=>P (T.cavityAssignment σ).1) a c=
      fullScalarCutGamma T U K a c*
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0 := by
  unfold nativeOriginalGammaWeightedExpectation
  rw [native_decoupled_rest_expect n q U b h K T ho P]

theorem native_original_gamma_rest_payload_eq_retained_first_high_and_remainders (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (hU : U ≤ as.length) :
    nativeOriginalGammaWeightedExpectation n 0 (cutFullVariance n q U 1 1 b h K) 0 U K T
      (fun σ=>P (T.cavityAssignment σ).1) a c=
      fullScalarCutGamma T U K a c*T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0+
      fullScalarCutGamma T U K a c*retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []+
      fullScalarCutGamma T U K a c*
        (∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K T
          (fun σ=>P (T.cavityAssignment σ).1) 0 0 2 t)+
      fullScalarCutGamma T U K a c*
        (∫l in (0:ℝ)..1,(1-l)*cutLowJet n q U b h K T
          (fun σ=>P (T.cavityAssignment σ).1) 0 2 l 1) := by
  unfold nativeOriginalGammaWeightedExpectation
  rw [native_rest_payload_low_restore_second n q U b h K T ho P
      hq0 hq hb hh hK hbm hhm hKm hU,
    native_rest_payload_high_taylor n q U b h K T ho P hq0 hq hb hh hK hbm hhm hKm]
  ring

theorem native_retained_first_high_eq_signed_rest_Gamma_rows (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) :
    retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []=
      ((T.markedAttach 0).map (fun e=>e.coeff*
        ((e.tree.markedAttach 0).map (fun f=>f.coeff*
          (f.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
            (insertedRestTest P (restHighKernel n U b h K) e f) 0*
            fullScalarCutGamma f.tree U K (f.embed e.mark) f.mark))).sum)).sum/2 := by
  simp only [retainedSignedJets,insertedSiteSlots,List.map_nil,List.nil_append,fullScalarCutGamma]

def nativeOriginalGammaProjectedDisplacement {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (K : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*
    nativeOriginalGammaWeightedExpectation n v q x U K p.tree
      (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
        A (T.atSlot (g.restrict (p.restrict σ)) s) (g.spin (p.restrict σ)))*
        P (g.restrict (p.restrict σ))) (p.embed (g.embed s)) p.mark)).sum

def nativeRetainedGammaProjectedDisplacement {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (nativeRestProjectedDisplacementTest T s star A P p) 0)).sum

def nativeGammaProjectedFirstHighDisplacement {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
      (nativeRestProjectedDisplacementTest T s star A P p) [])).sum

def nativeGammaProjectedHighSecondRestoration {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    (∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K p.tree
      (fun σ=>nativeRestProjectedDisplacementTest T s star A P p (p.tree.cavityAssignment σ).1)
      0 0 2 t))).sum

def nativeGammaProjectedLowSecondRestoration {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    (∫l in (0:ℝ)..1,(1-l)*cutLowJet n q U b h K p.tree
      (fun σ=>nativeRestProjectedDisplacementTest T s star A P p (p.tree.cavityAssignment σ).1)
      0 2 l 1))).sum

theorem native_original_gamma_projected_displacement_eq_retained_first_high_and_remainders
    (n : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ) (hU : U ≤ as.length)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalGammaProjectedDisplacement T s star U K 0
      (cutFullVariance n q U 1 1 b h K) 0 (fun σ τ=>A σ.1 τ.1)
      (fun σ=>P (T.cavityAssignment σ).1)=
      nativeRetainedGammaProjectedDisplacement T s star U q K A P+
      nativeGammaProjectedFirstHighDisplacement T s star U q b h K A P+
      nativeGammaProjectedHighSecondRestoration T s star U q b h K A P+
      nativeGammaProjectedLowSecondRestoration T s star U q b h K A P := by
  unfold nativeOriginalGammaProjectedDisplacement nativeRetainedGammaProjectedDisplacement
    nativeGammaProjectedFirstHighDisplacement nativeGammaProjectedHighSecondRestoration
    nativeGammaProjectedLowSecondRestoration
  dsimp only
  have Htest (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree) :
      (fun σ : p.tree.Assignment=>
        (A (p.spin σ).1 ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ)).1-
          A (T.atSlot ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ)) s).1
            ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ)).1)*
          P (T.cavityAssignment ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ))).1)=
      (fun σ=>nativeRestProjectedDisplacementTest T s star A P p (p.tree.cavityAssignment σ).1) := by
    funext σ
    exact (native_rest_projected_displacement_test_actual T s star A P p σ).symm
  simp_rw [Htest,native_original_gamma_rest_payload_eq_retained_first_high_and_remainders n q U b h K
    _ ho _ _ _ hq0 hq hb hh hK hbm hhm hKm hU]
  simp only [mul_add,List.sum_map_add]
  simp only [mul_assoc]

end OAI.SKFluctuations.Cavity
