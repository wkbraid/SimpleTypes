module Util
%default total

||| In defines propositional membership for Lists
data In : a -> List a -> Type where
  Here : In x (x :: xs)
  There : In x xs -> In x (y :: xs)

||| Relation is a Definition of a relation over a single type
Relation : Type -> Type
Relation a = a -> a -> Type

||| MultiStep defines the reflexive transitive closure of a relation
data MultiStep : Relation a -> Relation a where
  Reflexive : MultiStep r x x
  Transitive : r x y -> MultiStep r y z -> MultiStep r x z

syntax [x] THEN [y] = (x) `Transitive` (y)
