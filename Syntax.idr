module Simple.Syntax
import Util

%default total

||| SimpleType defines the internal type system
data SimpleType : Type where
  ARR : SimpleType -> SimpleType -> SimpleType

  UNIT : SimpleType


Variable : Type
Variable = String

||| Sugar defines the different levels of syntactic sugar available in the language
data Sugar = Core | Surface

||| AST defines internal syntax and syntactic sugar
data AST : Sugar -> Type where
  Var : Variable -> AST a
  Lam : Variable -> SimpleType -> AST a -> AST a
  App : AST a -> AST a -> AST a

  Unit : AST a

Term : Type
Term = AST Core

||| Value defines internal values in the language
data Value : Term -> Type where
  VLam : Value $ Lam x type term
  
  VUnit : Value $ Unit



||| Context defines a type context
Context : Type
Context = List (Variable, SimpleType)

syntax "{" [ctx] "|-" [term] ":" [type] "}" = TypeOf ctx term type

||| TypeOf defines the internal typing relation
data TypeOf : Context -> Term -> SimpleType -> Type where
  TVar : (x, type) `In` ctx -> { ctx |- (Var x) : type }
  TAbs : { ((x,type1) :: ctx) |- term : type2 } -> { ctx |- (Lam x type1 term) : type2 }
  TApp : { ctx |- term1 : (ARR type1 type2) } -> { ctx |- term2 : type1 } -> { ctx |- (App term1 term2) : type2 }

  TUnit : { ctx |- Unit : UNIT }
