/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/


import data.finset
import data.fintype.basic

open finset

variable {α : Type*}
variable {r : ℕ}

/-!
Basic definitions for finite sets which are useful for combinatorics.
We define antichains, and a proposition asserting that a set is a set of r-sets.
-/

/--
A family of sets is an antichain if no set is a subset of another. For example,
{{1}, {4,6,7}, {2,4,5,6}} is an antichain.
-/
def antichain (𝒜 : finset (finset α)) : Prop := ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ¬(A ⊆ B)

/-- `all_sized A r` states that every set in A has size r. -/
def all_sized (A : finset (finset α)) (r : ℕ) : Prop := ∀ x ∈ A, card x = r

/--
All sets in the union have size `r` iff both sets individually have this
property.
-/
lemma union_layer [decidable_eq α] {A B : finset (finset α)} :
  all_sized A r ∧ all_sized B r ↔ all_sized (A ∪ B) r :=
by simp only [all_sized, or_imp_distrib, forall_and_distrib, mem_union, iff_self]

/-- A couple of useful lemmas on fintypes -/

lemma mem_powerset_len_iff_card [fintype α] {r : ℕ} (x : finset α) :
  x ∈ powerset_len r (fintype.elems α) ↔ card x = r :=
by { rw mem_powerset_len, exact and_iff_right (subset_univ _) }

lemma powerset_len_iff_all_sized [fintype α] {𝒜 : finset (finset α)} :
  all_sized 𝒜 r ↔ 𝒜 ⊆ powerset_len r (fintype.elems α) :=
by rw all_sized; apply forall_congr _; intro A; rw mem_powerset_len_iff_card

lemma number_of_fixed_size [fintype α] {𝒜 : finset (finset α)} (h : all_sized 𝒜 r) :
  card 𝒜 ≤ nat.choose (fintype.card α) r :=
begin
  rw [fintype.card, ← card_powerset_len], apply card_le_of_subset,
  rwa [univ, ← powerset_len_iff_all_sized]
end