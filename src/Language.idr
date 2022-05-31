module Language

import Data.Vect

-- * Types
data Ty = TyInt
        | TyBool
        | TyFun Ty Ty

-- | notice in idris2 we can calculuate types simply and easily. This is
-- | basically injecting our type system Ty into the idris Type system! How cool
||| this is a doc string?
interpTy : Ty -> Type
interpTy TyInt       = Integer
interpTy TyBool      = Bool
interpTy (TyFun x y) = interpTy x -> interpTy y

||| variables are represented with De Bruijn indices. A HasType i ctxt ty is a
||| witness for the proof proof that variable i has type ty in context ctxt.
||| This is a basic inductive definition. Stop is proof that the most recently
||| defined variable is well-typed. Pop is is the inductive step, it is proof
||| that if the nth variable is well typed, so is the n+1th variable. Notice
||| that this grows just like a list, i.e., Pop (Pop Stop) is similar to Cons
||| (Cons Nil)
data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
     Stop : HasType FZ (t :: ctxt) t
     Pop  : HasType k ctxt t -> HasType (FS k) (u :: ctxt) t

||| an Expr is a GADT that will be indexed by local type variables. This is all
||| mostly self-explanatory
data Expr : Vect n Ty -> Ty -> Type where
     ||| If the variable i is well typed then we can conclude an Expr of type t
     Var : HasType i ctxt t -> Expr ctxt t
     ||| A value if only an Integer and is of type TyInt
     Val : (x : Integer) -> Expr ctxt TyInt

     ||| A lambda constructs a function from a -> t but notice that the ctxt is
     ||| not allowed to be empty, it must atleast be a singleton!
     Lam : Expr (a :: ctxt) t -> Expr ctxt (TyFun a t)

     ||| Application, we can only apply if we have an Expr of TyFun a -> t, and
     ||| an Expr of type T, again this is all pretty straightforward
     App : Expr ctxt (TyFun a t) -> Expr ctxt a -> Expr ctxt t

     ||| We include arbritrary binary operators where the type of the operator
     ||| dictates the type of the expression. I think we could also do this with
     ||| GADTs in Haskell
     Op  : (interpTy a -> interpTy b -> interpTy c)
            -> Expr ctxt a -> Expr ctxt b -> Expr ctxt c

     ||| An If, notice the Lazy!
     If  : Expr ctxt TyBool
           -> Lazy (Expr ctxt a) -> Lazy (Expr ctxt a) -> Expr ctxt a
