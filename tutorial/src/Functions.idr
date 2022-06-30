module Functions

import Data.Vect
import Data.Fin

%default total

traverseEither :  Semigroup e
               => (a -> Either e b)
               -> List a
               -> Either e (List b)
traverseEither f [] = Right []
traverseEither f (x :: xs) = case (f x , traverseEither f xs) of
  ((Left y), (Left z)) => Left $ y <+> z
  ((Right y), (Left z)) => Left z
  ((Left y), (Right z)) => Left y
  ((Right y), (Right z)) => Right $ y :: z

myhead : Vect (S n) a -> a
myhead (x :: xs) = x

myTail : Vect (S n) a -> Vect n a
myTail (x :: xs) = xs

myZipWith3 : (a -> b -> c -> d) -> Vect n a -> Vect n b -> Vect n c -> Vect n d
myZipWith3 f [] [] [] = []
myZipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: myZipWith3 f xs ys zs

myIndex : Fin n -> Vect n a -> a
myIndex FZ (x :: xs) = x
myIndex (FS x) (y :: xs) = myIndex x xs
