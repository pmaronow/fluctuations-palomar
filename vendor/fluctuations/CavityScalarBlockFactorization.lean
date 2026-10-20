module

public import CavityCutBlocks
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockZeroRefinement
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockRootMarginal

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
variable {S ι : Type} [Fintype S] [Fintype ι] [Nonempty S]

def slotProduct {as : List PositiveMass} (T : ClockTree S as) (f : S → ℝ)
    (σ : T.Assignment) : List T.Slot → ℝ
  | [] => 1
  | s::es => f (T.atSlot σ s)*slotProduct T f σ es

def leftSlotList {A B : Type} : List (A ⊕ B) → List A
  | [] => []
  | .inl a::es => a::leftSlotList es
  | .inr _::es => leftSlotList es

def rightSlotList {A B : Type} : List (A ⊕ B) → List B
  | [] => []
  | .inl _::es => rightSlotList es
  | .inr b::es => b::rightSlotList es

theorem mem_leftSlotList {A B : Type} (a : A) (es : List (A ⊕ B)) :
    a ∈ leftSlotList es ↔ Sum.inl a ∈ es := by
  induction es with
  | nil => simp [leftSlotList]
  | cons s es ih => cases s <;> simp [leftSlotList,ih]

theorem mem_rightSlotList {A B : Type} (b : B) (es : List (A ⊕ B)) :
    b ∈ rightSlotList es ↔ Sum.inr b ∈ es := by
  induction es with
  | nil => simp [rightSlotList]
  | cons s es ih => cases s <;> simp [rightSlotList,ih]

theorem leftSlotList_append {A B : Type} (es fs : List (A ⊕ B)) :
    leftSlotList (es++fs)=leftSlotList es++leftSlotList fs := by
  induction es with
  | nil => rfl
  | cons s es ih => cases s <;> simp [leftSlotList,ih]

theorem rightSlotList_append {A B : Type} (es fs : List (A ⊕ B)) :
    rightSlotList (es++fs)=rightSlotList es++rightSlotList fs := by
  induction es with
  | nil => rfl
  | cons s es ih => cases s <;> simp [rightSlotList,ih]

theorem slotProduct_step {as : List PositiveMass} (b : PositiveMass)
    (T : ClockTree S as) (f : S → ℝ) (σ : T.Assignment) (es : List T.Slot) :
    slotProduct (T.step b) f σ es=slotProduct T f σ es := by
  induction es with
  | nil => rfl
  | cons s es ih => simp only [slotProduct,atSlot,ih]

theorem slotProduct_fork {as : List PositiveMass} (T V : ClockTree S as)
    (f : S → ℝ) (σ : T.Assignment) (τ : V.Assignment)
    (es : List (T.Slot ⊕ V.Slot)) :
    slotProduct (T.fork V) f (σ,τ) es =
      slotProduct T f σ (leftSlotList es)*slotProduct V f τ (rightSlotList es) := by
  induction es with
  | nil => simp [slotProduct,leftSlotList,rightSlotList]
  | cons s es ih => cases s <;>
      simp only [slotProduct,leftSlotList,rightSlotList,atSlot,Sum.elim_inl,
        Sum.elim_inr,ih] <;> ring

theorem slotProduct_append {as : List PositiveMass} (T : ClockTree S as)
    (f : S → ℝ) (σ : T.Assignment) (es fs : List T.Slot) :
    slotProduct T f σ (es++fs)=slotProduct T f σ es*slotProduct T f σ fs := by
  induction es with
  | nil => simp [slotProduct]
  | cons s es ih => simp only [List.cons_append,slotProduct,ih]; ring

theorem expect_fork_product (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T V : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (P : T.Assignment → ℝ) (Q : V.Assignment → ℝ) (x : ι → ℝ) :
    (T.fork V).expect w φ q (fun σ=>P σ.1*Q σ.2) x =
      T.expect w φ q P x*V.expect w φ q Q x := by
  simp only [expect,weight_fork,Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem expect_slotProduct_fork (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T V : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (f : S → ℝ) (es : List (T.Slot ⊕ V.Slot)) (x : ι → ℝ) :
    (T.fork V).expect w φ q (fun σ=>slotProduct (T.fork V) f σ es) x =
      T.expect w φ q (fun σ=>slotProduct T f σ (leftSlotList es)) x*
      V.expect w φ q (fun σ=>slotProduct V f σ (rightSlotList es)) x := by
  have he : (fun σ=>(T.fork V).slotProduct f σ es) =
      (fun σ=>T.slotProduct f σ.1 (leftSlotList es)*V.slotProduct f σ.2 (rightSlotList es)) := by
    funext σ
    exact slotProduct_fork T V f σ.1 σ.2 es
  rw [he]
  exact expect_fork_product w φ T V q
    (fun σ=>T.slotProduct f σ (leftSlotList es))
    (fun σ=>V.slotProduct f σ (rightSlotList es)) x

theorem expect_slotProduct_cut_factor {w : S → ℝ} (hw : ∀ s, 0<w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → ι → ℝ≥0) (U : ℕ) (hU : U ≤ as.length) (hz : ∀ j, j+1 < U → q j=0)
    (f : S → ℝ) (es fs : List T.Slot)
    (hcross : ∀ s ∈ es, ∀ t ∈ fs, T.splitIndex s t < U) (x : ι → ℝ) :
    T.expect w φ q (fun σ=>slotProduct T f σ (es++fs)) x =
      T.expect w φ q (fun σ=>slotProduct T f σ es) x*
      T.expect w φ q (fun σ=>slotProduct T f σ fs) x := by
  induction T generalizing a q U with
  | leaf =>
    cases es with
    | nil => simp only [List.nil_append,slotProduct]; rw [expect_const hw φ _ ho]; ring
    | cons s es => cases fs with
      | nil => simp only [List.append_nil,slotProduct]; rw [expect_const hw φ _ ho]; ring
      | cons t fs =>
        have h:=hcross s (by simp) t (by simp)
        change 0 < U at h
        change U ≤ 0 at hU
        omega
  | @step b bs T ih =>
    by_cases hsmall : U ≤ 1
    · cases es with
      | nil => simp only [List.nil_append,slotProduct]; rw [expect_const hw φ _ ho]; ring
      | cons s es => cases fs with
        | nil => simp only [List.append_nil,slotProduct]; rw [expect_const hw φ _ ho]; ring
        | cons t fs =>
          have h:=hcross s (by simp) t (by simp)
          change 1+T.splitIndex s t<U at h
          omega
    · cases U with
      | zero => omega
      | succ U =>
        have hz0 : q 0=0 := hz 0 (by omega)
        have he (L : List T.Slot) : (T.step b).expect w φ q
            (fun σ=>slotProduct (T.step b) f σ L) x =
            T.expect w φ (fun j=>q (j+1)) (fun σ=>slotProduct T f σ L) x := by
          rw [expect_step hw φ b T ho.2.2]
          simp only [hz0,Pi.zero_apply,shiftedMean_zero_clock,slotProduct_step]
        rw [he,he,he]
        apply ih ho.2.2 (fun j=>q (j+1)) U (by simpa using hU)
        · intro j hj; exact hz (j+1) (by omega)
        · intro s hs t ht
          have h:=hcross s hs t ht
          change 1+T.splitIndex s t<U+1 at h
          omega
  | @fork bs T V ihT ihV =>
    simp only [expect_slotProduct_fork]
    rw [leftSlotList_append,rightSlotList_append,ihT ho q U hU hz,ihV ho q U hU hz]
    · ring
    · intro s hs t ht
      exact hcross (.inr s) ((mem_rightSlotList s es).mp hs)
        (.inr t) ((mem_rightSlotList t fs).mp ht)
    · intro s hs t ht
      exact hcross (.inl s) ((mem_leftSlotList s es).mp hs)
        (.inl t) ((mem_leftSlotList t fs).mp ht)

end OAI.SKFluctuations.Hierarchy.ClockTree
