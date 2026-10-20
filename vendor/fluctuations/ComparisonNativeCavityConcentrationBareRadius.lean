module

public import ComparisonNativeCavityConcentrationRadiusLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3000000

def cavityCanonicalFeatureEquiv (n : ℕ) :
    Fin (Fintype.card (FeatureIndex (n+1))-1+1) ≃ FeatureIndex (n+1) := by
  have hp : 0 < Fintype.card (FeatureIndex (n+1)) := Fintype.card_pos
  have he : Fintype.card (FeatureIndex (n+1))-1+1=Fintype.card (FeatureIndex (n+1)) := by omega
  exact (finCongr he).trans (Fintype.equivFin (FeatureIndex (n+1))).symm

theorem cavity_constant_clock_lipschitz {f alpha : ℝ → ℝ} {T a z : ℝ}
    (hf : ∀u,f u=T) : LipschitzOnWith 0 (fun r=>f (alpha r)) (Icc a z) := by
  have he : (fun r=>f (alpha r))=(fun _=>T) := funext (fun r=>hf (alpha r))
  rw [he]
  exact (LipschitzWith.const T).lipschitzOnWith

theorem actual_minimum_cavity_radius_Eq19_constant_clocks_tendsto_zero
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (a z : ℕ → ℝ) (ha : ∀n,0 < a n) (haz : ∀n,a n ≤ z n) (hz : ∀n,z n ≤ 1)
    (hxs1 : ∀n,(M n).xs ≤ 1) (hsize : ∀n,z n ≤ C*(M n).xs)
    (houter : ∀n,ca*(M n).xs ≤ (M n).alpha.val.val (a n))
    (T H : ℕ → ℝ) (hb_const : ∀n u,(M n).b u=T n) (hh_const : ∀n u,(M n).h u=H n) :
    Tendsto (fun n=>(M n).cavityRadiusDefect (a n) (z n)/(M n).xs^3) atTop (𝓝 0) := by
  exact actual_minimum_cavity_radius_Eq19_tendsto_zero Bclock hm hdelta hmargin hcl hcu
    hAz hC0 hCt hC hca M a z ha haz hz hxs1 hsize houter
    (fun n=>Fintype.card (FeatureIndex (n+1))-1) cavityCanonicalFeatureEquiv
    (fun _=>0) (fun _=>0)
    (fun n=>cavity_constant_clock_lipschitz (hb_const n))
    (fun n=>cavity_constant_clock_lipschitz (hh_const n))

theorem actual_minimum_cavity_radius_Eq19_bare_SK_tendsto_zero
    (Bclock T : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (a z : ℕ → ℝ) (ha : ∀n,0 < a n) (haz : ∀n,a n ≤ z n) (hz : ∀n,z n ≤ 1)
    (hxs1 : ∀n,(M n).xs ≤ 1) (hsize : ∀n,z n ≤ C*(M n).xs)
    (houter : ∀n,ca*(M n).xs ≤ (M n).alpha.val.val (a n))
    (hb_const : ∀n u,(M n).b u=T) (hh_zero : ∀n u,(M n).h u=0) :
    Tendsto (fun n=>(M n).cavityRadiusDefect (a n) (z n)/(M n).xs^3) atTop (𝓝 0) :=
  actual_minimum_cavity_radius_Eq19_constant_clocks_tendsto_zero Bclock hm hdelta hmargin
    hcl hcu hAz hC0 hCt hC hca M a z ha haz hz hxs1 hsize houter
    (fun _=>T) (fun _=>0) hb_const hh_zero

end OAI.SKFluctuations.LaplaceWindowFormalization
