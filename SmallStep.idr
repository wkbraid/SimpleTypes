module Simple.SmallStep
import Simple.Syntax
import Util

%default total

syntax [a] "=>>"  [b] = SmallStep a b
syntax [a] "=>>*" [b] = MultiStep SmallStep a b

||| SmallStep is the small step evaluation relation
data SmallStep : Term -> Term -> Type where

