module Util
import Data.Vect
import Data.Fin


%default total


||| At defines propositional indexing into vectors
data At : Fin n -> Vect n a -> a -> Type where
  Stop : At FZ (hd::tl) hd
  Pop  : At k tl x -> At (FS k) (u::tl) x



||| In defines propositional membership for Lists
data In : a -> List a -> Type where
  Here : In x (x :: xs)
  There : In x xs -> In x (y :: xs)

inEmpty : x `In` [] -> a
inEmpty Here impossible
inEmpty (There _) impossible


||| Relation is a Definition of a relation over a single type
Relation : Type -> Type
Relation a = a -> a -> Type

||| MultiStep defines the reflexive transitive closure of a relation
data MultiStep : Relation a -> Relation a where
  Reflexive : MultiStep r x x
  Transitive : r x y -> MultiStep r y z -> MultiStep r x z

syntax [x] THEN [y] = (x) `Transitive` (y)
