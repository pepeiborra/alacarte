{-#  OPTIONS_GHC -fglasgow-exts -fallow-overlapping-instances #-}
import Data.Maybe
import Control.Monad(liftM)
import Test.QuickCheck
import qualified Prelude (getChar,putChar,getLine,readFile,writeFile)
import Prelude hiding (getChar,putChar,getLine,readFile,writeFile)

infixr 6 :+:

main = putStrLn "It type checks."

data Expr f = In (f (Expr f))

data Val e = Val Int
type IntExpr = Expr Val

data Add e = Add e e
type AddExpr = Expr Add

data (f :+: g) e = Inl (f e) | Inr (g e) 

addExample :: Expr (Val :+: Add)
addExample = In (Inr (Add (In (Inl (Val 118))) (In (Inl (Val 1219)))))

instance Functor Val where
  fmap f (Val x) = Val x

instance Functor Add where
  fmap f (Add e1 e2) = Add (f e1) (f e2)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl e1)  = Inl (fmap f e1)
  fmap f (Inr e2)  = Inr (fmap f e2)

foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In t) = f (fmap (foldExpr f) t)

class Functor f => Eval f where
  evalAlgebra :: f Int -> Int

instance Eval Val where
  evalAlgebra (Val x) = x

instance Eval Add where
  evalAlgebra (Add x y) = x + y

instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlgebra (Inl x)  = evalAlgebra x
  evalAlgebra (Inr y)  = evalAlgebra y

eval :: Eval f => Expr f -> Int
eval expr = foldExpr evalAlgebra expr

infixl 6 <+>

class (Functor sub, Functor sup) => (:<:) sub sup where
  inj :: sub a -> sup a

instance Functor f => (:<:) f f where
  inj = id

instance (Functor f, Functor g) => (:<:) f (f :+: g) where
  inj = Inl

instance (Functor f, Functor g, Functor h, (:<:) f g) => 
  (:<:) f (h :+: g) where
    inj = Inr . inj

inject :: ((:<:) g f) => g (Expr f) -> Expr f
inject = In . inj

val :: ((:<:) Val f) => Int -> Expr f
val x      = inject (Val x)

(<+>) :: ((:<:) Add f) => Expr f -> Expr f -> Expr f
x <+> y    = inject (Add x y)

inVal :: Int -> Expr (Val :+: Val)
inVal i = inject (Val i)

data Mul x = Mul x x

instance Functor Mul where
  fmap f (Mul x y) = Mul (f x) (f y)

instance Eval Mul where
  evalAlgebra (Mul x y) = x * y

infixl 7 <*>
(<*>) :: ((:<:) Mul f) => Expr f -> Expr f -> Expr f
x <*> y  = inject (Mul x y)

class Render f where
  render :: Render g => f (Expr g) -> String

pretty :: Render f => Expr f -> String
pretty (In t) = render t

instance Render Val where
  render (Val i) = show i

instance Render Add where
  render (Add x y) = "(" ++ pretty x ++ " + " ++ pretty y ++ ")"

instance Render Mul where
  render (Mul x y) = "(" ++ pretty x ++ " * " ++ pretty y ++ ")"

instance (Render f, Render g) => Render (f :+: g) where
  render (Inl x) = render x
  render (Inr y) = render y

data Term f a = 
     Pure a 
  |  Impure (f (Term f a))

instance (Functor f) => Functor (Term f) where
  fmap f (Pure x)    = Pure (f x)
  fmap f (Impure t)  = Impure (fmap (fmap f) t)

instance (Functor f) => Monad (Term f) where
  return x           = Pure x
  (Pure x) >>= f     = f x
  (Impure t)  >>= f  = Impure (fmap (>>= f) t)

data Incr t = Incr Int t

data Recall t = Recall (Int -> t)

instance Functor Incr where
  fmap f (Incr i t) = Incr i (f t)  

instance Functor Recall where
  fmap f (Recall rc) = Recall (f . rc)

minject :: ((:<:) g f) => g (Term f a) -> Term f a
minject = Impure . inj

incr :: ((:<:) Incr f) => Int -> Term f ()
incr i = minject (Incr i (Pure ()))

recall :: ((:<:) Recall f) => Term f Int
recall = minject (Recall Pure)

tick :: Term (Recall :+: Incr) Int
tick = do  y <- recall
           incr 1
           return y

foldTerm :: Functor f => (a -> b) -> (f b -> b) -> Term f a -> b
foldTerm pure imp (Pure x)     = pure x
foldTerm pure imp (Impure t)   = imp (fmap (foldTerm pure imp) t)    

newtype Mem = Mem Int

instance Show Mem where
  show (Mem x) = "Mem " ++ show x 

class Functor f => Run f where
  runAlgebra :: f (Mem -> (a,Mem)) -> (Mem -> (a,Mem))

instance Run Incr where
  runAlgebra (Incr k r) (Mem i) = r (Mem (i + k))

instance Run Recall where
  runAlgebra (Recall r) (Mem i) = r i (Mem i)

instance (Run f, Run g) => Run (f :+: g) where
  runAlgebra (Inl r) = runAlgebra r
  runAlgebra (Inr r) = runAlgebra r

run :: Run f => Term f a -> Mem -> (a,Mem)
run = foldTerm (,) runAlgebra 

data Teletype a = 
     GetChar (Char -> a)
  |  PutChar Char a

data FileSystem a =
     ReadFile FilePath (String -> a)
  |  WriteFile FilePath String a

exec :: Exec f => Term f a -> IO a
exec = foldTerm return execAlgebra

class Functor f => Exec f where
  execAlgebra :: f (IO a) -> IO a

instance Exec Teletype where
  execAlgebra (GetChar f)     = Prelude.getChar >>= f
  execAlgebra (PutChar c io)  = Prelude.putChar c >> io

cat ::  FilePath ->  Term (Teletype :+: FileSystem) ()
cat fp = do
  contents <- readFile fp
  mapM putChar contents
  return ()

instance Functor Teletype where
  fmap f (GetChar g) = GetChar (f . g)
  fmap f (PutChar c x) = PutChar c (f x) 

instance Functor FileSystem where
  fmap f (ReadFile fp g) = ReadFile fp (f . g)
  fmap f (WriteFile fp g io) = WriteFile fp g (f io)

getChar :: ((:<:) Teletype f) => Term f Char
getChar = minject (GetChar Pure)

putChar :: ((:<:) Teletype f) => Char -> Term f ()
putChar c = minject (PutChar c (Pure ()))

readFile :: ((:<:) FileSystem f) => FilePath -> Term f String
readFile fp = minject (ReadFile fp Pure)

writeFile :: ((:<:) FileSystem f) => FilePath -> String -> Term f ()
writeFile fp str = minject (WriteFile fp str (Pure ()))

instance Exec FileSystem where
  execAlgebra (ReadFile fp g) = Prelude.readFile fp >>= g
  execAlgebra (WriteFile fp str x) = Prelude.writeFile fp str >> x

instance (Exec f, Exec g) => Exec (f :+: g) where
  execAlgebra (Inl x) = execAlgebra x
  execAlgebra (Inr y) = execAlgebra y

getLine :: ((:<:) Teletype f) => Term f String
getLine = do
  c <- getChar
  if c == '\n'
    then return []
    else getLine >>= \cs -> return (c : cs)
