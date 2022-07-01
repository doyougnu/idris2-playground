||| What do we have in the domain?
||| we have state: the directory
||| we have streams that are composed by pipes
||| we have commands but not all commands are equal
||| cd is special, it sets state
||| ls, ll, cat, are stream producers
||| grep, awk, sed, are stream transformers
||| >, >>, are stream consumers
||| but whats file? What do we do when we use something like 'strip'?
||| strip takes a file, alters it, and puts it back
||| so what if files are special 0arity functions that return a stream of file contents?

||| then they wouldn't compose (which makes sense) but would be stream producers
||| and we would probably have a nice applicative instance

||| Aha so then is a directory just a set of files (of functions)?!?!?!
||| then cd changes the set, ls and ll transform the set into a producer stream

||| but then what about things like relative paths: ../ and . these must refer
||| to previous candidates in a stack of sets, or perhaps a tree if we used a
||| zipper. But a tree doesn't really buy us anything because combining a set
||| and a stack makes a rose tree

module Main

import Data.Vect
import Data.Maybe
import Data.Stream
import System

import Decidable.Equality

%default total

||| A type synonym for a paths
Path : Type
Path = String

||| A type synonym for Commands
Command : Type
Command = String

||| A type synonym for Command arguments
Arguments : Type
Arguments = String

CommandArgs : Type
CommandArgs = List Arguments

||| A Directory is a dependently typed set of names. It dependently typed by the
||| path to the directory and each element of the type is a file that resides in
||| the directory.
data Directory : (p : Path) -> Type where
  Protected   : (p : Path) -> Directory p
  UnProtected : (p : Path) -> Directory p

||| because we index Directory with the path no two directories can ever be
||| equal and so this is a tautology.
implementation Eq (Directory p) where
  (==) (Protected p)   (Protected p)   = p == p
  (==) (UnProtected p) (UnProtected p) = p == p
  (==) _ _ = False

root : Directory "/"
root = Protected "/"

||| Proof that a directory is not the Root directory
public export
data NotProtected : (d : Directory p) -> Type where
  IsNotProtected : NotProtected (UnProtected d)

Uninhabited (NotProtected (Protected p)) where
  uninhabited IsNotProtected impossible

data StreamTy = StdIn
              | StdOut
              | StdErr

data Cmd : (c : Command) -> StreamTy -> Type where
  MkCmd : (c : Command) -> (args : CommandArgs) -> (t : StreamTy) -> Cmd c t

-- data HasType : (i : Fin n) -> Vect n CmdTy -> CmdTy -> Type where
--   Here  : HasType FZ (t :: ctxt) t
--   There : HasType k ctxt t -> HasType (FS k) (u :: ctxt) t

data Shell : Directory p -> StreamTy -> Type where
  ShCmd : Cmd c t -> Shell ctxt t
  Pipe : Shell ctx t -> Shell ctx' t' -> Shell ctx' t'

home : Directory "~"
home = Protected "~"

programming : Directory "~/programming"
programming = UnProtected "~/programming"

cd : (new : Directory p) -> Shell new StdOut
cd (Protected p) = ShCmd (MkCmd p neutral StdOut)
cd (UnProtected p) = ShCmd (MkCmd p neutral StdOut)

wc : CommandArgs -> Shell here StdOut
wc args = ShCmd (MkCmd "wc" args StdOut)

toHome : Shell Main.home StdOut
toHome = cd home

rm : (to_remove : Directory p)
   -> CommandArgs
   -> {auto 0 prf : NotProtected to_remove}
   -> Shell here StdOut
rm (UnProtected p) args = ShCmd (MkCmd p args StdOut)

ex : Shell s StdOut
ex = rm programming ["rf"]

main : IO ()
main = do
  path <- System.system "date \"+%d%m%Y\""
  putStrLn $ "Oi: " ++ show path

-- n) safety checks
-- -- i) that we have a remote
-- -- ii) that the branch name doesn't already exist
-- 1) branch from wip/js-staging with name wip/js-staging-bkup-date
-- 2) generate date with System.system "date \"+%d%m%Y\""
-- 3) push the branch
-- 4) switch back

-- sys : HasIO io => (cmd : String) -> EitherT Err io ()
-- sys cmd = do
--   0 <- system cmd | n => throwE (Sys cmd n)
--   pure ()

-- git : List String -> Either Err

