


class Recursive (Base : outParam (Type → Type)) (T : Type) extends Functor Base where
  project : T → Base T
  cata {β} : (Base β → β) → T → β
