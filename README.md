
# Recursion Schemes

Based on the [recursion-schemes package](https://github.com/recursion-schemes/recursion-schemes) for Haskell.
See also: https://github.com/leanprover-community/mathlib4/pull/282

## Plan:

Given a recursive inductive datatype,

I think that I can get quite far by asking for the following:
- Given an inductive datatype `T` with a constructor `𝑐` and arg `𝑎 : α`, derive
	- `T.𝑐.𝑎? : T → Option α`
	- `T.𝑐.𝑎! [Inhabited α] : T → α`
	- `T.𝑎? : T → Option α` maps each constructor with arg `𝑎` to this.
	- `T.𝑎! : T → α`
    - `T.Pos`
	- `T.children : T → List T`
	- `T.traverseChildren`
	- `T.Base : Type → Type` is the base functor type such that `T = Fix T.Base`
	- `T.Free : Type → Type`
	- `T.Cofree : Type → Type`
	- `T.Zipper`

1.