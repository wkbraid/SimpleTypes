module Simple.SmallStep
import Syntax
import Util

%default total


syntax "[" [var] "/" [val] "]" [term] = substitute var val term

||| substitute defines substition over terms
substitute : Variable -> Term -> Term -> Term
substitute x val (Var y) = case decEq x y of
                                Yes _ => val
                                No _ => Var y
substitute x val (Lam y type body) = case decEq x y of
                                          Yes _ => Lam y type body -- shadowing
                                          No _ => Lam y type ([x / val] body)
substitute x val (App left right) = App ([x / val] left) ([x / val] right)
substitute x val Unit = Unit
-- TODO: definitely includes variable capture



syntax [a] "=>>"  [b] = SmallStep a b
syntax [a] "=>>*" [b] = MultiStep SmallStep a b

||| SmallStep is the small step evaluation relation
data SmallStep : Term -> Term -> Type where
  EApp1 : (left1 =>> left2) -> (App left1 right) =>> (App left2 right)
  EApp2 : Value left -> (right1 =>> right2) -> (App left right1) =>> (App left right2)
  EAppAbs : Value arg -> (App (Lam x type body) arg) =>> [x / arg] body



