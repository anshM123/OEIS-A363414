import DMSolutions.OEIS_A363414.Solution

/-!
# Checks for the solution of `OeisA363414.conjecture_type1_empty`

* The definition copied into `A363414Core` is the statement file's definition (`rfl`).
* `conjecture_type1_empty_solved` has exactly the type of the repository statement
  `conjecture_type1_empty`.
* `conjecture_type1_empty_solved` uses only the standard axioms.
-/

-- The copied definition agrees with the statement file's definition.
example : OeisA363414.a = A363414Core.a := rfl

-- `conjecture_type1_empty_solved` has exactly the type of the repository statement.
example : type_of% @OeisA363414.conjecture_type1_empty =
    type_of% @OeisA363414.conjecture_type1_empty_solved := rfl

-- The repository statement and ours, printed for comparison:
#check @OeisA363414.conjecture_type1_empty
#check @OeisA363414.conjecture_type1_empty_solved

#print axioms OeisA363414.conjecture_type1_empty_solved
