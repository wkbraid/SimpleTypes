module Simple.SmallStep
import Syntax
import Util

%default total


syntax "[" [var] "/" [val] "]" [term] = substitute var val term

||| substitute defines substition over terms
substitute : Variable -> Term -> Term -> Term



syntax [a] "=>>"  [b] = SmallStep a b
syntax [a] "=>>*" [b] = MultiStep SmallStep a b

||| SmallStep is the small step evaluation relation
data SmallStep : Term -> Term -> Type where
  EApp1 : (left1 =>> left2) -> (App left1 right) =>> (App left2 right)
  EApp2 : (right1 =>> right2) -> (App left right1) =>> (App left right2)
  EAppAbs : (App (Lam x type body) arg) =>> [x / arg] body



