module

public meta import Lean

/-!
# The `granville_moore` tag attribute

`@[granville_moore "TAG"]` records that a declaration formalizes the result labelled `TAG` of A.
Granville, *The p-divisibility of the integer Moore determinant and iterated Fermat quotients*. A
result whose content is spread over several declarations carries the tag on each of them, so that
their union is exactly the tagged statement; auxiliary declarations are left untagged.

    @[granville_moore "thm_main"]
    theorem my_result : True := trivial
-/

public meta section

open Lean

/-- `@[granville_moore "TAG"]` records that a declaration formalizes the result labelled
`TAG` of the source paper. -/
syntax (name := granville_moore) "granville_moore " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `granville_moore
  descr := "marks a declaration as formalizing a result of the source paper"
  add   := fun _ _ _ => pure ()
}

end
