module IO

import Data.List
import Data.String
import Data.Vect

import System.File

%default total

hello : IO ()
hello = putStrLn "hello world"

readHello : IO ()
readHello = do
  name <- getLine
  putStrLn $ "Hello " ++ name
