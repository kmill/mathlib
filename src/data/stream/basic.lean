/-
Copyright (c) 2020 Gabriel Ebner, Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Simon Hudon
-/

import tactic.ext data.stream data.list.basic

/-!
# Additional instances and attributes for streams
-/

attribute [ext] stream.ext

instance {α} [inhabited α] : inhabited (stream α) :=
⟨stream.const (default _)⟩

namespace stream
open nat

def take_aux {α} : stream α → ℕ → list α → list α
| s 0 xs := xs.reverse
| s (succ n) xs := take_aux s.tail n (s.head :: xs)

def take {α} (s : stream α) (n : ℕ) : list α :=
take_aux s n []

lemma length_take_aux {α} : Π (n : ℕ) (s : stream α) (xs : list α),
  (take_aux s n xs).length = n + xs.length
| 0 s xs := by rw [take_aux,list.length_reverse _,nat.zero_add]
| (succ n) s xs := by simp [take_aux,length_take_aux n,succ_eq_add_one]

lemma length_take {α} (s : stream α) (n : ℕ) : (take s n).length = n :=
length_take_aux n s []

end stream
