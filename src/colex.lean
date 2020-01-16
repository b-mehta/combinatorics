/- 
The colex ordering for finite sets
-/

import data.finset
import data.fintype
import algebra.geom_sum

variable {α : Type*}

open finset

/- The colex ordering likes to avoid large numbers. For us, it's mostly used for sets of a fixed size. If the
size is 3, colex on ℕ starts 123, 124, 134, 234, 125, 135, 235, 145, 245, 345, ... -/

def colex_lt [has_lt α] (A B : finset α) : Prop := ∃ (k : α), (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B
def colex_le [has_lt α] (A B : finset α) : Prop := colex_lt A B ∨ A = B
infix ` <ᶜ `:50 := colex_lt
infix ` ≤ᶜ `:50 := colex_le

lemma colex_hom {β : Type*} [linear_order α] [decidable_eq β] [preorder β] {f : α → β} (h₁ : strict_mono f) (A B : finset α) : 
  image f A <ᶜ image f B ↔ A <ᶜ B :=
begin
  simp [colex_lt],
  split,
    rintro ⟨k, z, q, k', _, rfl⟩, 
    refine ⟨k', λ x hx, _, λ t, q _ t rfl, ‹k' ∈ B›⟩, have := z (h₁ hx), simp [strict_mono.injective h₁] at this, assumption,
  rintro ⟨k, z, _, _⟩, 
  refine ⟨f k, λ x hx, _, _, k, ‹k ∈ B›, rfl⟩, 
  split, any_goals { 
    rintro ⟨x', x'in, rfl⟩, refine ⟨x', _, rfl⟩,
    rwa ← z _ <|> rwa z _, rwa strict_mono.lt_iff_lt h₁ at hx }, 
  simp [strict_mono.injective h₁], exact λ x hx, ne_of_mem_of_not_mem hx ‹k ∉ A›
end

-- this special case shows up a lot
lemma colex_hom_fin {n : ℕ} (A B : finset (fin n)) : image fin.val A <ᶜ image fin.val B ↔ A <ᶜ B := colex_hom (λ x y k, k) _ _

instance [has_lt α] : is_irrefl (finset α) (<ᶜ) := ⟨λ A h, exists.elim h (λ _ q, q.2.1 q.2.2)⟩
instance [has_lt α] : is_refl (finset α) (≤ᶜ) := ⟨λ A, or.inr rfl⟩
instance [linear_order α] : is_trans (finset α) (<ᶜ) := 
begin
  constructor,
  rintros A B C ⟨k₁, k₁z, notinA, inB⟩ ⟨k₂, k₂z, notinB, inC⟩,
  have: k₁ ≠ k₂ := ne_of_mem_of_not_mem inB notinB,
  cases lt_or_gt_of_ne this,
    refine ⟨k₂, _, by rwa k₁z h, inC⟩, 
    intros x hx, rw ← k₂z hx, apply k₁z (trans h hx), 
  refine ⟨k₁, _, notinA, by rwa ← k₂z h⟩, 
  intros x hx, rw k₁z hx, apply k₂z (trans h hx)
end
instance [linear_order α] : is_asymm (finset α) (<ᶜ) := by apply_instance
instance [linear_order α] : is_antisymm (finset α) (≤ᶜ) := ⟨λ A B AB BA, AB.elim (λ k, BA.elim (λ t, (asymm k t).elim) (λ t, t.symm)) id⟩
instance [linear_order α] : is_trans (finset α) (≤ᶜ) := ⟨λ A B C AB BC, AB.elim (λ k, BC.elim (λ t, or.inl (trans k t)) (λ t, t ▸ AB)) (λ k, k.symm ▸ BC)⟩
instance [linear_order α] : is_strict_order (finset α) (<ᶜ) := {}
instance [decidable_linear_order α] : is_trichotomous (finset α) (<ᶜ) :=
begin
  constructor,
  intros A B, 
  set diff := (A \ B) ∪ (B \ A),
  by_cases h: diff = ∅,
    right, left,
    apply subset.antisymm,
    any_goals { rw ← sdiff_eq_empty_iff_subset, rw ← subset_empty, rw ← h }, 
      apply subset_union_left,
    apply subset_union_right,
  set k := max' diff h,
  have := max'_mem diff h, simp only [mem_union, mem_sdiff] at this,
  rcases this with ⟨_, _⟩ | ⟨_, _⟩,
    right, right, swap, left,
  all_goals 
  { refine ⟨k, _, ‹_›, ‹_›⟩,
    intros x hx, by_contra,
    apply not_le_of_lt hx,
    apply le_max', simp only [mem_union, mem_sdiff],
    tauto }
end
-- TODO: is there a way of doing totality of ≤ without trichotomy of <? I think we need trichotomy of < on α but there might be another way
instance [decidable_linear_order α] : is_total (finset α) (≤ᶜ) := ⟨λ A B, (trichotomous A B).elim3 (or.inl ∘ or.inl) (or.inl ∘ or.inr) (or.inr ∘ or.inl)⟩
instance [decidable_linear_order α] : is_linear_order (finset α) (≤ᶜ) := {}
instance [decidable_linear_order α] : is_incomp_trans (finset α) (<ᶜ) :=
begin
  constructor,
  rintros A B C ⟨nAB, nBA⟩ ⟨nBC, nCB⟩, 
  have: A = B, apply or.resolve_right (or.resolve_left (trichotomous A B) nAB) nBA, 
  have: B = C, apply or.resolve_right (or.resolve_left (trichotomous B C) nBC) nCB, 
  rw [‹A = B›, ‹B = C›], rw and_self, apply irrefl
end
instance [decidable_linear_order α] : is_strict_weak_order (finset α) (<ᶜ) := {}
instance [decidable_linear_order α] : is_strict_total_order (finset α) (<ᶜ) := {}
instance colex_order [has_lt α] : has_le (finset α) := {le := (≤ᶜ)}
instance colex_preorder [linear_order α] : preorder (finset α) := {le_refl := refl_of (≤ᶜ), le_trans := is_trans.trans, ..colex_order}
instance colex_partial_order [linear_order α] : partial_order (finset α) := {le_antisymm := is_antisymm.antisymm, ..colex_preorder}
instance colex_linear_order [decidable_linear_order α] : linear_order (finset α) := {le_total := is_total.total (≤ᶜ), ..colex_partial_order}

instance colex_lt_decidable [decidable_linear_order α] [fintype α] (A B : finset α) : decidable (A <ᶜ B) := by rw colex_lt; apply_instance
instance colex_le_decidable [decidable_linear_order α] [fintype α] (A B : finset α) : decidable (A ≤ᶜ B) := or.decidable
instance colex_decidable_order [decidable_linear_order α] [fintype α] : decidable_linear_order (finset α) := {decidable_le := infer_instance, ..colex_linear_order}

/- If A is before B in colex, and everything in B is small, then everything in A is small. -/
lemma max_colex [decidable_linear_order α] {A B : finset α} (t : α) (h₁ : A <ᶜ B) (h₂ : ∀ x ∈ B, x < t) : ∀ x ∈ A, x < t := 
begin
  rw colex_lt at h₁, rcases h₁ with ⟨k, z, _, _⟩,
  intros x hx, apply lt_of_not_ge, intro, apply not_lt_of_ge a, apply h₂, rwa ← z, apply lt_of_lt_of_le (h₂ k ‹_›) a, 
end

lemma binary_sum_nat {k : ℕ} {A : finset ℕ} (h₁ : ∀ {x}, x ∈ A → x < k) : A.sum (pow 2) < 2^k :=
begin
  apply lt_of_le_of_lt (sum_le_sum_of_subset (λ t, mem_range.2 ∘ h₁)),
  have z := geom_sum_mul_add 1 k, rw [geom_series, mul_one] at z, 
  simp only [nat.pow_eq_pow] at z, rw ← z, apply nat.lt_succ_self
end

-- We have an equivalent relation to the colex order, for subsets of ℕ.
-- Note this gives a proof that <ᶜ is decidable for α = ℕ, which we didn't have before.
lemma binary_iff (A B : finset ℕ) : A.sum (pow 2) < B.sum (pow 2) ↔ A <ᶜ B :=
begin
  have z: ∀ (A B : finset ℕ), A <ᶜ B → A.sum (pow 2) < B.sum (pow 2),
    rintro A B ⟨k, maxi, notinA, inB⟩,
    have AeqB: A.filter (λ x, ¬(x ≤ k)) = B.filter (λ x, ¬(x ≤ k)),
    { ext t, by_cases h: (k < t); simp [h], apply maxi h },
    have Alt: (A.filter (λ x, x ≤ k)).sum (pow 2) < pow 2 k :=
      binary_sum_nat (λ _, (λ th, lt_of_le_of_ne (and.right th) (ne_of_mem_of_not_mem th.left notinA)) ∘ mem_filter.1), 
    have leB: pow 2 k ≤ (B.filter (λ x, x ≤ k)).sum (pow 2),
    { apply single_le_sum (λ _ _, nat.zero_le _) (mem_filter.2 ⟨inB, _⟩), refl },
    have := add_lt_add_right (lt_of_lt_of_le Alt leB) ((filter (λ x, ¬(x ≤ k)) A).sum (pow 2)),
    rwa [← sum_union, filter_union_filter_neg_eq, AeqB, ← sum_union, filter_union_filter_neg_eq] at this, 
    any_goals { rw disjoint_iff_inter_eq_empty, apply filter_inter_filter_neg_eq },
  refine ⟨λ h, (trichotomous A B).resolve_right (λ h₁, h₁.elim _ (λ q, not_lt_of_gt h (z _ _ q))), z A B⟩, 
  rintro rfl, apply irrefl _ h
end

-- lemma union_empty_iff (A B : finset α) [decidable_eq α]: A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ := lattice.sup_eq_bot_iff

-- lemma sym_diff_empty_iff_eq [decidable_eq α] (A B : finset α) : A \ B ∪ B \ A = ∅ ↔ A = B :=
-- begin
--   rw union_empty_iff, rw sdiff_eq_empty_iff_subset, rw sdiff_eq_empty_iff_subset, rw subset.antisymm_iff
-- end

-- example [decidable_linear_order α] (A B : finset α) : A ≤ᶜ B ↔ dite (A = B) (λ _, true) (λ t, max' (A \ B ∪ B \ A) (mt (sym_diff_empty_iff_eq _ _).1 t) ∈ B) :=
-- begin
--   split_ifs, rw iff_true, right, assumption,
--   split; intro p, obtain ⟨k, z, h₁, h₂⟩ := p.resolve_right h, convert h₂, apply le_antisymm, 
--   apply max'_le, intros t th, apply le_of_not_lt, intro a, specialize z a, simp at th z, tauto,
--   apply le_max', simp [h₁, h₂], 
--   left, refine ⟨_, _, _, p⟩, intros t th, by_contra, rw [not_iff, iff_iff_and_or_not_and_not, not_not] at a, apply not_le_of_lt th, 
--   apply le_max', simp, rwa [or_comm, and_comm], 
--   intro, have := max'_mem (A \ B ∪ B \ A) _, simp [p, a] at this, assumption, exact mt (sym_diff_empty_iff_eq _ _).1 h,
-- end