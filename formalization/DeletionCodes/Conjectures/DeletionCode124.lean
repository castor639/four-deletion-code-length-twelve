import DeletionCodes.Conjectures.DeletionCode124Data

/-!
# Exact binary length-12 four-deletion code

## Sorry inventory

- None.

## Claim

In the ordinary ordered fixed-length deletion model, `A_2(12,4) = 6`.

Words are encoded by `Fin 4096`; `bitList 12` is their fixed-width binary
representation.  A length-8 word is a four-deletion descendant exactly when
its fixed-width bit list is a `List.isSublist` of the length-12 bit list.

The lower witness and upper certificate are transparent data in
`DeletionCode124Data.lean`.  `native_decide` checks only finite leaf facts
about that explicit data: the six-word witness, the twenty conflict cliques,
all 4,096 coverage inequalities, and the total weight.  The weighted-packing
argument from those facts to the universal nonexistence of a seven-word code
is proved below in Lean.  Consequently the formal artifact inherits
`native_decide`'s compiler/runtime trust boundary; the standalone exact
Python checker provides an independent verification path.
-/

namespace DeletionCodes.Conjectures.DeletionCode124

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev Word := Fin 4096
abbrev Descendant := Fin 256
abbrev CutIndex := Fin 20

/-- Fixed-width, most-significant-bit-first binary representation. -/
def bitList (width value : Nat) : List Bool :=
  (List.range width).map fun index => Nat.testBit value (width - 1 - index)

/-- Whether `descendant` is an ordered length-8 subsequence of `word`. -/
def hasDescendant (descendant word : Nat) : Bool :=
  (bitList 8 descendant).isSublist (bitList 12 word)

/-- Two words conflict when they share a length-8 deletion descendant. -/
def conflicts (left right : Nat) : Bool :=
  (List.range 256).any fun descendant =>
    hasDescendant descendant left && hasDescendant descendant right

/-- A labelled family is a valid ordinary four-deletion code. -/
def ValidFamily {size : Nat} (code : Fin size → Word) : Prop :=
  Function.Injective code ∧
  ∀ left right, left ≠ right → conflicts (code left).val (code right).val = false

def descendantWeight (descendant : Descendant) : Nat :=
  descendantWeights.getD descendant.val 0

def cutAt (index : CutIndex) : Nat × List Nat :=
  cliqueCuts.getD index.val (0, [])

def cutWeight (index : CutIndex) : Nat := (cutAt index).1

def cutWords (index : CutIndex) : List Nat := (cutAt index).2

def descendantCoverage (word : Nat) : Nat :=
  ∑ descendant : Descendant,
    if hasDescendant descendant.val word = true then descendantWeight descendant else 0

def cutCoverage (word : Nat) : Nat :=
  ∑ index : CutIndex,
    if word ∈ cutWords index then cutWeight index else 0

/-- Exact integer coverage assigned to one possible length-12 word. -/
def coverage (word : Nat) : Nat := descendantCoverage word + cutCoverage word

def totalWeight : Nat :=
  (∑ descendant : Descendant, descendantWeight descendant) +
  (∑ index : CutIndex, cutWeight index)

def cliqueValid (words : List Nat) : Bool :=
  words.all fun left =>
    words.all fun right => (left == right) || conflicts left right

def explicitCodeValid (words : List Nat) : Bool :=
  words.all (fun word => word < 4096) &&
  words.all fun left =>
    words.all fun right => (left == right) || !(conflicts left right)

/-! ## Finite certificate checks -/

theorem checked_lower_code :
    lowerCode.Nodup ∧ lowerCode.length = 6 ∧ explicitCodeValid lowerCode = true := by
  native_decide

theorem checked_all_cliques : ∀ index : CutIndex, cliqueValid (cutWords index) = true := by
  native_decide

theorem checked_all_coverage :
    ∀ word : Word, certificateDenominator ≤ coverage word.val := by
  native_decide

theorem checked_total_weight :
    totalWeight = 6999616 ∧ totalWeight < 7 * certificateDenominator := by
  native_decide

/-! ## Leaf lemmas connecting the checked data to packing inequalities -/

lemma conflicts_of_common_descendant {descendant left right : Nat}
    (hd : descendant < 256)
    (hl : hasDescendant descendant left = true)
    (hr : hasDescendant descendant right = true) :
    conflicts left right = true := by
  simp only [conflicts, List.any_eq_true, Bool.and_eq_true]
  exact ⟨descendant, List.mem_range.mpr hd, hl, hr⟩

lemma cut_is_valid (index : CutIndex) : cliqueValid (cutWords index) = true := by
  exact checked_all_cliques index

lemma cut_conflicts {index : CutIndex} {left right : Nat}
    (hl : left ∈ cutWords index) (hr : right ∈ cutWords index)
    (hne : left ≠ right) : conflicts left right = true := by
  have hleft := (List.all_eq_true.mp (cut_is_valid index)) left hl
  have hright := (List.all_eq_true.mp hleft) right hr
  simp only [Bool.or_eq_true, beq_iff_eq] at hright
  exact hright.resolve_left hne

def descendantHitCount (code : Fin 7 → Word) (descendant : Descendant) : Nat :=
  ∑ index : Fin 7,
    if hasDescendant descendant.val (code index).val = true then 1 else 0

def cutHitCount (code : Fin 7 → Word) (index : CutIndex) : Nat :=
  ∑ position : Fin 7, if (code position).val ∈ cutWords index then 1 else 0

lemma descendant_hit_count_le_one {code : Fin 7 → Word}
    (valid : ValidFamily code) (descendant : Descendant) :
    descendantHitCount code descendant ≤ 1 := by
  unfold descendantHitCount
  rw [Finset.sum_boole]
  rw [Nat.cast_id]
  rw [Finset.card_le_one_iff]
  intro left right hl hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl hr
  by_contra hne
  have hconflict := conflicts_of_common_descendant descendant.isLt hl hr
  rw [valid.2 left right hne] at hconflict
  exact Bool.noConfusion hconflict

lemma cut_hit_count_le_one {code : Fin 7 → Word}
    (valid : ValidFamily code) (index : CutIndex) :
    cutHitCount code index ≤ 1 := by
  unfold cutHitCount
  rw [Finset.sum_boole]
  rw [Nat.cast_id]
  rw [Finset.card_le_one_iff]
  intro left right hl hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl hr
  by_contra hne
  have hword : (code left).val ≠ (code right).val := by
    intro hval
    exact hne (valid.1 (Fin.ext hval))
  have hconflict := cut_conflicts hl hr hword
  rw [valid.2 left right hne] at hconflict
  exact Bool.noConfusion hconflict

def descendantFamilyWeight (code : Fin 7 → Word) : Nat :=
  ∑ descendant : Descendant,
    descendantWeight descendant * descendantHitCount code descendant

def cutFamilyWeight (code : Fin 7 → Word) : Nat :=
  ∑ index : CutIndex, cutWeight index * cutHitCount code index

def familyWeightedCount (code : Fin 7 → Word) : Nat :=
  descendantFamilyWeight code + cutFamilyWeight code

lemma sum_descendant_coverage (code : Fin 7 → Word) :
    (∑ position : Fin 7, descendantCoverage (code position).val) =
      descendantFamilyWeight code := by
  unfold descendantCoverage descendantFamilyWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro descendant _
  calc
    (∑ position : Fin 7,
        if hasDescendant descendant.val (code position).val = true
        then descendantWeight descendant else 0) =
        ∑ position : Fin 7, descendantWeight descendant *
          (if hasDescendant descendant.val (code position).val = true then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro position _
            split <;> simp_all
    _ = descendantWeight descendant *
        (∑ position : Fin 7,
          if hasDescendant descendant.val (code position).val = true then 1 else 0) := by
            rw [Finset.mul_sum]
    _ = descendantWeight descendant * descendantHitCount code descendant := by
            rfl

lemma sum_cut_coverage (code : Fin 7 → Word) :
    (∑ position : Fin 7, cutCoverage (code position).val) = cutFamilyWeight code := by
  unfold cutCoverage cutFamilyWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  calc
    (∑ position : Fin 7,
        if (code position).val ∈ cutWords index then cutWeight index else 0) =
        ∑ position : Fin 7, cutWeight index *
          (if (code position).val ∈ cutWords index then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro position _
            split <;> simp_all
    _ = cutWeight index *
        (∑ position : Fin 7,
          if (code position).val ∈ cutWords index then 1 else 0) := by
            rw [Finset.mul_sum]
    _ = cutWeight index * cutHitCount code index := by
            rfl

lemma sum_coverage_eq_family_weighted_count (code : Fin 7 → Word) :
    (∑ position : Fin 7, coverage (code position).val) = familyWeightedCount code := by
  simp only [coverage, familyWeightedCount, Finset.sum_add_distrib,
    sum_descendant_coverage, sum_cut_coverage]

lemma family_weighted_count_le_total {code : Fin 7 → Word}
    (valid : ValidFamily code) : familyWeightedCount code ≤ totalWeight := by
  apply Nat.add_le_add
  · apply Finset.sum_le_sum
    intro descendant _
    simpa using Nat.mul_le_mul_left (descendantWeight descendant)
      (descendant_hit_count_le_one valid descendant)
  · apply Finset.sum_le_sum
    intro index _
    simpa using Nat.mul_le_mul_left (cutWeight index)
      (cut_hit_count_le_one valid index)

/-! ## Universal upper bound and exact theorem -/

theorem no_valid_seven_word_code : ¬ ∃ code : Fin 7 → Word, ValidFamily code := by
  rintro ⟨code, valid⟩
  have lower : 7 * certificateDenominator ≤
      ∑ position : Fin 7, coverage (code position).val := by
    calc
      7 * certificateDenominator = ∑ _position : Fin 7, certificateDenominator := by
        simp
      _ ≤ ∑ position : Fin 7, coverage (code position).val := by
        exact Finset.sum_le_sum fun position _ => checked_all_coverage (code position)
  have upper : (∑ position : Fin 7, coverage (code position).val) ≤ totalWeight := by
    rw [sum_coverage_eq_family_weighted_count]
    exact family_weighted_count_le_total valid
  have total_lt := checked_total_weight.2
  omega

/--
Faithful exact result: the explicit list is a valid six-word code, and no
labelled family of seven distinct compatible words exists.  Any larger code
would contain such a seven-word subfamily, so this is `A_2(12,4) = 6`.
-/
theorem binary_length12_four_deletion_exact :
    (lowerCode.Nodup ∧ lowerCode.length = 6 ∧ explicitCodeValid lowerCode = true) ∧
    ¬ ∃ code : Fin 7 → Word, ValidFamily code :=
  ⟨checked_lower_code, no_valid_seven_word_code⟩

#print axioms binary_length12_four_deletion_exact

end DeletionCodes.Conjectures.DeletionCode124
