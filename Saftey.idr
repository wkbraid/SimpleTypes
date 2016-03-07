module Simple.Saftey
import Syntax
import SmallStep
import Util

%default total


progress : {[] |- a : type} -> Either (Value a) (b ** (a =>> b))
progress (TVar prf) = inEmpty prf
progress (TAbs _) = Left VLam
progress (TApp left {term1=lterm} right {term2=rterm}) = 
  case progress left of
    Right (left2 ** step) => Right (App left2 rterm ** EApp1 step)
    Left lvalprf => case progress right of
                         Right (right2 ** step) => Right (App lterm right2 ** EApp2 step)
                         Left rvalprf => Right ?appProgress
progress TUnit = Left VUnit


subpreserve : {((x, subtype)::c) |- term : type} -> {c |- subterm : subtype} -> {c |- ([x/subterm]term) : type}

preservation : (a =>> b) -> {[] |- a : type} -> {[] |- b : type}
