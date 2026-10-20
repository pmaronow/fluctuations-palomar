module

public import ComparisonSignedCavityActualOriginalGPairRestoration
public import ComparisonSignedCavityActualOriginalHighResponse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000

theorem native_original_high_pairing_eq_connected_rest_payload (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length) :
    nativeOriginalHighPairing n v q x U K b C T P a c=
      nativeOriginalConnectedHighResponse n v q x U K b C T
        (fun σ=>P (T.cavityAssignment σ).1) a c := by
  rw [←native_original_G_rows_eq_connected_response n v q x U K b C T ho
    (fun σ=>P (T.cavityAssignment σ).1) a c hU]
  unfold nativeOriginalHighPairing
  simp_rw [ClockTree.MarkedPlacement.restRestrict_actual]

theorem native_decoupled_connected_response_eq_retained (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length) :
    nativeOriginalConnectedHighResponse n 0 (cutFullVariance n q U 0 0 b h K) 0 U K b C T
      (fun σ=>P (T.cavityAssignment σ).1) a c=
      nativeRetainedHighPairing n q U b h K T P a c := by
  rw [←native_original_high_pairing_eq_connected_rest_payload n 0
    (cutFullVariance n q U 0 0 b h K) 0 U K b C T ho P a c hU]
  change nativeDecoupledOriginalGPairing n q U b h K C T P a c=_
  exact (native_retained_high_pairing_eq_decoupled_original_G n q U b h K C hKC T ho P a c hU).symm

theorem native_original_connected_response_eq_retained_add_restoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalConnectedHighResponse n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b C T
      (fun σ=>P (T.cavityAssignment σ).1) a c=
      nativeRetainedHighPairing n q U b h K T P a c+
      nativeOriginalHighPairRestoration n q U b h K C T P a c := by
  rw [←native_original_high_pairing_eq_connected_rest_payload n 0
    (cutFullVariance n q U 1 1 b h K) 0 U K b C T ho P a c hU]
  exact native_original_high_pairing_eq_retained_add_restoration n q U b h K C hKC
    T ho P a c hU hq0 hq hb hh hK hbm hhm hKm

theorem native_original_connected_rows_eq_retained_add_restoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : (p : ClockTree.MarkedPlacement T)→p.tree.cavityLeft.Assignment→ℝ)
    (a : T.Slot) (hU : U ≤ as.length)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    ((T.markedAttach 0).map (fun p=>p.coeff*
      nativeOriginalConnectedHighResponse n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b C p.tree
        (fun σ=>P p (p.tree.cavityAssignment σ).1) (p.embed a) p.mark)).sum=
    ((T.markedAttach 0).map (fun p=>p.coeff*
      nativeRetainedHighPairing n q U b h K p.tree (P p) (p.embed a) p.mark)).sum+
    ((T.markedAttach 0).map (fun p=>p.coeff*
      nativeOriginalHighPairRestoration n q U b h K C p.tree (P p) (p.embed a) p.mark)).sum := by
  simp_rw [native_original_connected_response_eq_retained_add_restoration n q U b h K C hKC
    _ ho _ _ _ hU hq0 hq hb hh hK hbm hhm hKm]
  simp only [mul_add,List.sum_map_add]

end OAI.SKFluctuations.Cavity
