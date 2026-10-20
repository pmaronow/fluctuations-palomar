module

public import CavityMomentAllocation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy

 theorem finite_weighted_mean_abs_pow_le {A : Type*} [Fintype A] (w F : A → ℝ)
    (hw : ∀ a, 0≤w a) (hmass : ∑ a, w a=1) (m : ℕ) :
    |∑ a, w a*F a|^m≤∑ a, w a*|F a|^m := by
  have H : |∑ a, w a*F a|≤∑ a, w a*|F a| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
    apply Finset.sum_congr rfl
    intro a _
    rw [abs_mul,abs_of_nonneg (hw a)]
  have J := (convexOn_pow (𝕜:=ℝ) m).map_sum_le
    (t:=Finset.univ) (w:=w) (p:=fun a=>|F a|) (fun a _=>hw a) hmass
    (fun a _=>abs_nonneg (F a))
  exact (pow_le_pow_left₀ (abs_nonneg _) H m).trans (by simpa only [smul_eq_mul] using J)

 theorem finite_weighted_centered_abs_pow_le {A : Type*} [Fintype A] (w F : A → ℝ)
    (hw : ∀ a, 0≤w a) (hmass : ∑ a, w a=1) {m : ℕ} (hm : 0 < m) :
    (∑ a, w a*|F a-(∑ b, w b*F b)|^m)≤(2:ℝ)^m*(∑ a, w a*|F a|^m) := by
  let c := ∑ b, w b*F b
  have H := finite_weighted_mean_abs_pow_le w F hw hmass m
  have Hpoint (a : A) : |F a-c|^m≤(2:ℝ)^(m-1)*(|F a|^m+|c|^m) := by
    apply (pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) m).trans
    exact add_pow_le (abs_nonneg _) (abs_nonneg _) m
  have HH := Finset.sum_le_sum fun a (_ : a∈Finset.univ)=>mul_le_mul_of_nonneg_left (Hpoint a) (hw a)
  have he : (∑ a, w a*((2:ℝ)^(m-1)*(|F a|^m+|c|^m)))=
      (2:ℝ)^(m-1)*((∑ a, w a*|F a|^m)+|c|^m) := by
    calc
      _=(2:ℝ)^(m-1)*((∑ a, w a*|F a|^m)+|c|^m*(∑ a, w a)) := by
        simp only [Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _=_ := by rw [hmass,mul_one]
  rw [he] at HH
  apply HH.trans
  have hpow : (2:ℝ)^(m-1)*2=(2:ℝ)^m := by rw [←pow_succ]; congr 1; omega
  dsimp only [c] at H ⊢
  have HI := mul_le_mul_of_nonneg_left H (by positivity : 0≤(2:ℝ)^(m-1))
  calc
    _≤(2:ℝ)^(m-1)*((∑ a, w a*|F a|^m)+(∑ a, w a*|F a|^m)) := by linarith
    _=_ := by rw [show ((∑ a, w a*|F a|^m)+(∑ a, w a*|F a|^m))=2*(∑ a, w a*|F a|^m) by ring,
      ←mul_assoc,hpow]

namespace ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S]
 theorem disorderExpect_centered_abs_pow_le {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) (T : ClockTree S as)
    (F : T.Assignment → ℝ) {m : ℕ} (hm : 0 < m) :
    T.disorderExpect w φ v q (fun σ=>|F σ-T.disorderExpect w φ v q F x|^m) x≤
      (2:ℝ)^m*T.disorderExpect w φ v q (fun σ=>|F σ|^m) x := by
  exact finite_weighted_centered_abs_pow_le (fun σ=>T.disorderWeight w φ v q σ x) F
    (T.disorderWeight_probability hw φ ho v q x).1
    (T.disorderWeight_probability hw φ ho v q x).2 hm
end ClockTree
end OAI.SKFluctuations.Hierarchy
