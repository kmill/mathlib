/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import data.set.basic
import algebra.group.basic
variables {α : Type*} {β : Type*} {γ : Type*}
/-! # Group operations on sets

## Main Definitions

* For `s t : set α` we have `s.mul t`, which is `st = { x * y | x ∈ s, y ∈ t }`.
* For `s : set α` we have `s.inv`, which is `s⁻¹ = { x⁻¹ | x ∈ s }`.
* The additive versions are `s.add t` and `s.neg`.

## Implementation Notes

* For convenience `s.inv` is implemented as a preimage (since preimages are better behaved).
  Use `inv_image` to rewrite it to a image.
-/

namespace set

/-- The pointwise product of two sets `s` and `t`:
  `st = s ⬝ t = s * t = { x * y | x ∈ s, y ∈ t }. -/
@[to_additive "The pointwise sum of two sets `s` and `t`: `s + t = { x + y | x ∈ s, y ∈ t }."]
protected def mul [has_mul α] (s t : set α) : set α :=
(λ p : α × α, p.1 * p.2) '' s.prod t

@[simp, to_additive] lemma mem_mul [has_mul α] {s t : set α} {x : α} :
  x ∈ s.mul t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x :=
by { simp only [set.mul, and.assoc, mem_image, mem_prod, prod.exists] }

@[to_additive] lemma mul_mem_mul [has_mul α] {s t : set α} {x y : α} (hx : x ∈ s) (hy : y ∈ t) :
  x * y ∈ s.mul t :=
by { simp only [mem_mul], exact ⟨x, y, hx, hy, rfl⟩ }

@[simp, to_additive add_image_prod]
lemma mul_image_prod [has_mul α] (s t : set α) : (λ p : α × α, p.1 * p.2) '' s.prod t = s.mul t :=
rfl

@[to_additive]
lemma mul_subset_mul [has_mul α] {s t u v : set α} (h1 : u ⊆ s) (h2 : v ⊆ t) :
  u.mul v ⊆ s.mul t :=
by { apply image_subset, simp only [prod_subset_prod_iff, h1, h2, true_or, and_self], }

/-- The pointwise inverse of a set `s`: `s⁻¹ = { x⁻¹ | x ∈ s }. -/
@[to_additive "The pointwise additive inverse of a set `s`: `s⁻¹ = { x⁻¹ | x ∈ s }"]
protected def inv [has_inv α] (s : set α) : set α :=
has_inv.inv ⁻¹' s

@[simp, to_additive] lemma mem_inv [has_inv α] {s : set α} {x : α} :
  x ∈ s.inv ↔ x⁻¹ ∈ s :=
by { simp only [set.inv, mem_preimage] }

@[to_additive] lemma inv_mem_inv [group α] {s : set α} {x : α} : x⁻¹ ∈ s.inv ↔ x ∈ s :=
by simp only [mem_inv, inv_inv]

@[simp, to_additive]
lemma inv_preimage [has_inv α] (s : set α) : has_inv.inv ⁻¹' s = s.inv :=
rfl

@[simp, to_additive]
lemma inv_image [group α] (s : set α) : has_inv.inv '' s = s.inv :=
by refine congr_fun (image_eq_preimage_of_inverse _ _) s; intro; simp only [inv_inv]

@[simp, to_additive] protected lemma inv_inv [group α] {s : set α} : s.inv.inv = s :=
by { simp only [set.inv, ← preimage_comp], convert preimage_id, ext x, apply inv_inv }

@[simp, to_additive] protected lemma univ_inv [group α] : (univ : set α).inv = univ :=
preimage_univ

end set
