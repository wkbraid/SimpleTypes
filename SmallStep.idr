module Simple.SmallStep
import Data.Fin
import Data.Vect
import Syntax
import Util

%default total



bind : (ctx:Vect (S n) a) -> At k ctx _ -> Vect n a
bind (hd::tl) Stop = tl
bind (hd::tl) (Pop inner) = ?top

syntax "[" [var] "/" [val] "]" [term] = substitute var val term

||| substitute defines substituion of values into expressions
substitute : At k ctx vty -> Expr Nil vty -> Expr ctx ty -> Expr ctx ty
--substitute Stop val (Var Stop) = val

substitute at val (Lam body) = Lam ([(Pop at)/val]body)
substitute at val (App left right) = App ([at/val]left) ([at/val]right)
substitute at val Unit = Unit

-- substitue [0/val] (var 0) => val, but have to make sure types work out
-- so in the ctx, 0 better have type of val



--substitute : Variable -> Term -> Term -> Term
--substitute x val (Var y) = case decEq x y of
                                --Yes _ => val
                                --No _ => Var y
--substitute x val (Lam y type body) = case decEq x y of
                                          --Yes _ => Lam y type body -- shadowing
                                          --No _ => Lam y type ([x / val] body)
--substitute x val (App left right) = App ([x / val] left) ([x / val] right)
--substitute x val Unit = Unit
-- TODO: definitely includes variable capture



--syntax [a] "=>>"  [b] = SmallStep a b
--syntax [a] "=>>*" [b] = MultiStep SmallStep a b

--data SmallStep : Term -> Term -> Type where
  --EApp1 : (left1 =>> left2) -> (App left1 right) =>> (App left2 right)
  --EApp2 : Value left -> (right1 =>> right2) -> (App left right1) =>> (App left right2)
  --EAppAbs : Value arg -> (App (Lam x type body) arg) =>> [x / arg] body



