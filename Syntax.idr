module Simple.Syntax
import Data.Vect
import Data.Fin
import Util

%default total

||| SimpleType defines the internal type system
data Ty : Type where
  ARR : Ty -> Ty -> Ty 
  UNIT : Ty


||| Expr defines internal syntax in terms of number of free variables
data Expr : Vect n Ty -> Ty -> Type where
  Var : At idx ctx t -> Expr ctx t
  Lam : Expr (t1 :: ctx) t2 -> Expr ctx (t1 `ARR` t2)
  App : Expr ctx (t1 `ARR` t2) -> Expr ctx t1 -> Expr ctx t2

  Unit : Expr ctx UNIT


||| Value defines internal values in the language
data Value : Expr Nil type -> Type where
  VLam : Value $ Lam body 
  VUnit : Value $ Unit
