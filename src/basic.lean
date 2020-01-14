/- 
Basic definitions for finite sets which are useful for combinatorics.
-/

import data.finset
import data.fintype

open finset

variable {α : Type*}
variable {r : ℕ}

/- A family of sets is an antichain if no set is a subset of another -/
def antichain (𝒜 : finset (finset α)) : Prop := ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ¬(A ⊆ B)

/- `all_sized A r` states that every set in A has size r -/
def all_sized (A : finset (finset α)) (r : ℕ) : Prop := ∀ x ∈ A, card x = r

lemma union_layer [decidable_eq α] {A B : finset (finset α)} : all_sized A r ∧ all_sized B r ↔ all_sized (A ∪ B) r :=
begin
  split; intros p, 
    rw all_sized,
    intros,
    rw mem_union at H,
    exact H.elim (p.1 _) (p.2 _),
  split,
  all_goals {rw all_sized, intros, apply p, rw mem_union, tauto}, 
end

lemma mem_powerset_len_iff_card [fintype α] {r : ℕ} : ∀ (x : finset α), x ∈ powerset_len r (fintype.elems α) ↔ card x = r :=
by intro x; rw mem_powerset_len; exact and_iff_right (subset_univ _)

lemma powerset_len_iff_all_sized [fintype α] {𝒜 : finset (finset α)} : all_sized 𝒜 r ↔ 𝒜 ⊆ powerset_len r (fintype.elems α) :=
begin
  rw all_sized, apply forall_congr _, intro A, rw mem_powerset_len_iff_card
end

lemma number_of_fixed_size [fintype α] {𝒜 : finset (finset α)} (h : all_sized 𝒜 r) : card 𝒜 ≤ nat.choose (fintype.card α) r :=
begin
  rw [fintype.card, ← card_powerset_len],
  apply card_le_of_subset,
  rwa [univ, ← powerset_len_iff_all_sized]
end