module

public import ComparisonSignedCavityOriginalConnectedLawAdapter
public import ComparisonSignedCavityActualOriginalGProjectedRow

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000

def nativeRestProjectedDisplacementTest {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (τ : p.tree.cavityLeft.Assignment) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  (A (p.restSpin τ) (g.restSpin (p.restRestrict τ))-
    A (T.cavityLeft.atSlot (g.restRestrict (p.restRestrict τ)) (T.cavityLeftSlot s))
      (g.restSpin (p.restRestrict τ)))*P (g.restRestrict (p.restRestrict τ))

theorem native_rest_projected_displacement_test_actual {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree) (σ : p.tree.Assignment) :
    nativeRestProjectedDisplacementTest T s star A P p (p.tree.cavityAssignment σ).1=
      (A (p.spin σ).1 ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ)).1-
        A (T.atSlot ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ)) s).1
          ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ)).1)*
        P (T.cavityAssignment ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ))).1 := by
  dsimp only [nativeRestProjectedDisplacementTest]
  rw [←p.restSpin_actual,←p.restRestrict_actual,
    ←(nativeFreshAtSlot T 0 s star).restSpin_actual,
    ←(nativeFreshAtSlot T 0 s star).restRestrict_actual,T.atSlot_cavityLeft]

def nativeRetainedGProjectedDisplacement {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*
    nativeRetainedHighPairing n q U b h K p.tree
      (nativeRestProjectedDisplacementTest T s star A P p) (p.embed (g.embed s)) p.mark)).sum

def nativeOriginalGProjectedDisplacementRestoration {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*
    nativeOriginalHighPairRestoration n q U b h K C p.tree
      (nativeRestProjectedDisplacementTest T s star A P p) (p.embed (g.embed s)) p.mark)).sum

theorem native_original_G_projected_displacement_eq_retained_add_restoration
    (n : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j) (hU : U ≤ as.length)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeActualOriginalGProjectedDisplacement T s star U K b C 0
      (cutFullVariance n q U 1 1 b h K) 0 (fun σ τ=>A σ.1 τ.1)
      (fun σ=>P (T.cavityAssignment σ).1)=
      nativeRetainedGProjectedDisplacement T s star U q b h K A P+
      nativeOriginalGProjectedDisplacementRestoration T s star U q b h K C A P := by
  unfold nativeActualOriginalGProjectedDisplacement nativeRetainedGProjectedDisplacement
    nativeOriginalGProjectedDisplacementRestoration
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
  simp_rw [Htest]
  exact native_original_connected_rows_eq_retained_add_restoration n q U b h K C hKC
    (nativeFreshAtSlot T 0 s star).tree ho (nativeRestProjectedDisplacementTest T s star A P)
    ((nativeFreshAtSlot T 0 s star).embed s) hU hq0 hq hb hh hK hbm hhm hKm

end OAI.SKFluctuations.Cavity
