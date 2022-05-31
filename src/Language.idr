module Language

-- * Types
data Ty = TyInt
        | TyBool
        | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt       = Integer
interpTy TyBool      = Bool
interpTy (TyFun x y) = interpTy x -> interpTy y
