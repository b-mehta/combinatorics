import data.finset
import data.fintype

variable {α : Type*}

open finset

def colex_order [has_lt α] (A B : finset α) : Prop := ∃ (k : α), (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B
infix ` <ᶜ `:50 := colex_order

lemma colex_hom {β : Type*} [linear_order α] [decidable_eq β] [preorder β] {f : α → β} (h₁ : strict_mono f) (A B : finset α) : 
  image f A <ᶜ image f B ↔ A <ᶜ B :=
begin
  simp [colex_order],
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
instance [decidable_linear_order α] [fintype α] (A B : finset α) : decidable (A <ᶜ B) :=
by rw colex_order; apply_instance
instance colex_decidable_rel [decidable_linear_order α] [fintype α] : decidable_rel ((<ᶜ) : finset α → finset α → Prop) :=
by intros A B; apply_instance

lemma max_colex [decidable_linear_order α] {A B : finset α} (t : α) (h₁ : A <ᶜ B) (h₂ : ∀ x ∈ B, x < t) : ∀ x ∈ A, x < t := 
begin
  rw colex_order at h₁, rcases h₁ with ⟨k, z, _, _⟩,
  intros x hx, apply lt_of_not_ge, intro, apply not_lt_of_ge a, apply h₂, rwa ← z, apply lt_of_lt_of_le (h₂ k ‹_›) a, 
end