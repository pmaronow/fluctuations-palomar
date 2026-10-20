module

public import ComparisonVirtualGapLimitExistence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 14000000

structure ComparisonVirtualGapFiniteConditions
    (a b B K : ℝ) (C : ℝ≥0) (left right errors : ℕ→ℝ)
    (H J G : ℕ→ℝ→ℝ) (n : ℕ) : Prop where
  left_lower : a-1 ≤ left n
  left_upper : left n ≤ B
  right_mem : right n ∈ Icc a B
  ordered : left n ≤ right n
  left_zero : H n (left n)=0
  right_zero : H n (right n)=0
  lipschitz : LipschitzOnWith C (H n) (Icc (left n) B)
  lower_error : ∀t∈Icc a b,-errors n ≤ H n (max (left n) t)
  factor_monotone : MonotoneOn (J n) (Icc a B)
  factor_bound : ∀t∈Icc a B,J n t∈Icc (1/K^2) (K^2)
  factor_measurable : Measurable (J n)
  gradient_integrable : ∀s∈Ioo a b,∀t∈Ioo a b,s ≤ t → IntegrableOn (G n) (Icc s t)
  primitive : ∀s∈Ioo a b,∀t∈Ioo a b,left n ≤ s → s ≤ t →
    H n t-H n s=∫r in s..t,J n r*G n r

 theorem comparison_virtual_gap_limit_exists_of_eventual
    {a b B K : ℝ} {C : ℝ≥0} (hab : a < b) (hbB : b < B) (hK : 1 ≤ K)
    (left right errors : ℕ→ℝ) (H J G : ℕ→ℝ→ℝ) (f : ℝ→ℝ)
    (hleft : Tendsto left atTop (𝓝 a)) (hright : Tendsto right atTop (𝓝 b))
    (herr : Tendsto errors atTop (𝓝 0))
    (hf : IntegrableOn f (Icc a b))
    (hGlim : ∀s∈Ioo a b,∀t∈Ioo a b,s ≤ t →
      Tendsto (fun n=>∫r in Icc s t,|G n r-f r|) atTop (𝓝 0))
    (hfinite : ∀ᶠn in atTop,ComparisonVirtualGapFiniteConditions a b B K C left right errors H J G n) :
    ∃j : ℝ→ℝ,Monotone j ∧ (∀t∈Icc a b,j t∈Icc (1/K^2) (K^2)) ∧
      Nonempty (ComparisonPinnedGapPrimitive a b (fun t=>j t*f t)) := by
  obtain ⟨n0,Hn0⟩:=eventually_atTop.mp hfinite
  let phi : ℕ→ℕ:=fun n=>n+n0
  have hphi : Tendsto phi atTop atTop:=tendsto_add_atTop_nat n0
  have Htail n : ComparisonVirtualGapFiniteConditions a b B K C left right errors H J G (phi n):=
    Hn0 (phi n) (by dsimp only [phi];omega)
  exact comparison_virtual_gap_limit_exists hab hbB hK
    (left ∘ phi) (right ∘ phi) (errors ∘ phi) (H ∘ phi) (J ∘ phi) (G ∘ phi) f
    (fun n=>(Htail n).left_lower) (fun n=>(Htail n).left_upper)
    (hleft.comp hphi) (hright.comp hphi)
    (fun n=>(Htail n).right_mem) (fun n=>(Htail n).ordered)
    (fun n=>(Htail n).left_zero) (fun n=>(Htail n).right_zero)
    (fun n=>(Htail n).lipschitz) (herr.comp hphi)
    (fun n=>(Htail n).lower_error) (fun n=>(Htail n).factor_monotone)
    (fun n=>(Htail n).factor_bound) (fun n=>(Htail n).factor_measurable)
    hf (fun n s t hs ht hst=>(Htail n).gradient_integrable s hs t ht hst)
    (fun s t hs ht hst=>(hGlim s hs t ht hst).comp hphi)
    (fun n s t hs ht hls hst=>(Htail n).primitive s hs t ht hls hst)

end OAI.SKFluctuations.LaplaceWindowFormalization
