

/-!

Reference:
- https://www.cambridge.org/core/services/aop-cambridge-core/content/view/3FC26EB2A63E6A2B29E07B9F0D5C5BCD/S0956796809007291a.pdf/the-essence-of-the-iterator-pattern.pdf


 -/

class Bifunctor (P : Type → Type → Type) where
  bimap {A B C D} : (A → B) → (C → D) → (P A C) → (P B D)

open Bifunctor

-- [todo] P is outParam
class BaseBifunctor (P : outParam (Type → Type → Type)) (F : Type → Type) where
  inn {A} : P A (F A) → F A
  out {A} : F A → P A (F A)
  -- and they are inverses

inductive List.Base (A : Type) (B : Type)
  | nil
  | cons (head : A) (tail : B)

instance : Bifunctor List.Base where
  bimap f g := fun | List.Base.nil => List.Base.nil | List.Base.cons h t => List.Base.cons (f h) (g t)

instance : BaseBifunctor List.Base List where
  inn := fun | List.Base.nil => List.nil | List.Base.cons h t => List.cons h t
  out := fun | List.nil => List.Base.nil | List.cons h t => List.Base.cons h t

open BaseBifunctor

variable {P} [Bifunctor P] {F} [BaseBifunctor P F]

namespace Origami

partial def map [Inhabited (F B)] (f : A → B) (fa : F A) : F B :=
   inn <| bimap f (map f) <| out <| fa

partial def fold [Inhabited B] (f : P A B → B) (fa : F A) : B :=
  f <| bimap id (fold f) <| out <| fa

partial def unfold [Inhabited (F A)] (f : B → P A B) (b : B) : F A :=
  inn <| bimap id (unfold f) <| f <| b

end Origami

#eval Origami.map (Nat.succ) [1,2,3,4,5]
#eval Origami.unfold (F := List) (A := Nat) (fun n : Nat => match n with | 0 => List.Base.nil | (n+1) => List.Base.cons n n) 10