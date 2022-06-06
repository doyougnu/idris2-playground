module Interpreter

import Language

import Data.Vect

data Env : Vect n Ty -> Type where
  Nil  : Env Nil
  (::) : interpTy a -> Env ctxt -> Env (a :: ctxt)

lookup : HasType i ctxt ty -> Env ctxt -> interpTy ty
lookup Stop    (x :: xs) = x
lookup (Pop k) (x :: xs) = lookup k xs

||| interp maps values in the object domain Expr to Idris. Classic EDSL design
interp : Env ctxt -> Expr ctxt ty -> interpTy ty
interp env (Var i)    = lookup i env
interp env (Val x)    = x
interp env (Lam sc)   = \y => interp (y :: env) sc
interp env (App f y)  = interp env f (interp env y)
interp env (Op f x y) = f (interp env x) (interp env y)
interp env (If c t e) = if (interp env c)
                        then interp env t
                        else interp env e

||| ayy it works!
add : Expr ctxt (TyFun TyInt (TyFun TyInt TyInt))
add = Lam (Lam (Op (+) (Var Stop) (Var (Pop Stop))))
