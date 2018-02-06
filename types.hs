{-# LANGUAGE TupleSections #-}

import Data.List (find)
import Data.Maybe (mapMaybe, fromMaybe)
import Control.Monad (join)
import Control.Applicative ((<|>))


-- Inductive definition: T = V | T → T
data Type = TVar String | TArr Type Type deriving (Eq)


instance Show Type where
  show (TVar x) = x
  show (TArr l@(TArr _ _) r) = "(" ++ show l ++ ")→" ++ show r
  show (TArr l            r) =        show l ++  "→" ++ show r


-- Some nice constructors, operators, properties
-- not used in the algorithm, but in tests.

-- n = ((0 → …) → 0) → 0
fromNum :: Integer -> Type
fromNum 0 = TVar "0"
fromNum n = TArr (fromNum (n - 1)) (fromNum 0)

-- a^k → b = a → (a^{k-1} → b)
pow :: Type -> Integer -> Type -> Type
pow _ 0 b = b
pow a k b = TArr a (pow a (k - 1) b)

-- n^k = (n-1)^k → 0
nk :: Integer -> Integer -> Type
nk 0 _ = fromNum 0
nk n k = pow (fromNum $ n - 1) k (fromNum 0)

-- depth of binary tree with (→) in nodes
dpt :: Type -> Integer
dpt (TVar _)   = 1
dpt (TArr l r) = 1 + max (dpt l) (dpt r)

rnk :: Type -> Integer
rnk (TVar _)   = 0
rnk (TArr l r) = max (1 + rnk l) (rnk r)

ord :: Type -> Integer
ord = (+1) . rnk

s  = pow (fromNum 1) 2 (fromNum 3)



-- splitArrows (a → (b → c) → d) = [a, b→c, d]
splitArrows :: Type -> [Type]
splitArrows t@(TVar _) = [t]
splitArrows (TArr l r) = l : splitArrows r


type Arr = (Maybe Type, Type)

mkArrow :: Maybe Type -> Type -> Type
mkArrow Nothing t  = t
mkArrow (Just l) t = TArr l t

-- subarrows ((a→b)→c) = [(Nothing, (a→b)→c), (Just (a→b), c)]
subArrows :: Type -> [Arr]
subArrows type' = zip left right
  where
    s     = splitArrows type'
    right = scanr1 TArr s
    left  = Nothing : (Just <$> scanl1 TArr s)


-- subArrowTo c (a→b)→c = (Just (a→b), c)
subArrowTo :: Type -> Type -> Maybe Arr
subArrowTo t type' = find ((t ==) . snd) (subArrows type')


type Var = String

type Decl = (Var, Type) -- y:a→b

type Context = [Decl]   -- Г = { x:a, y:a→b }


ctxSubArrowTo :: Context -> Type -> [(Var, Arr)]
ctxSubArrowTo ctx t = mapMaybe (traverse (subArrowTo t)) ctx


type Hole = (Type, Context)

data NFHole =
  Hole Hole |              -- L(B; Г)
  HoleAbstr Decl NFHole |  -- λx:A. L(B; Г,x:A)
  HoleApp   Decl [NFHole]  -- x L(B₁; Г) ··· L(Bn; Г)
  deriving (Show, Eq)

expand :: NFHole -> [NFHole]
expand (Hole (a@(TVar _), ctx)) = map apps (ctxSubArrowTo ctx a)
  where
    holesFrom  :: Type -> [Hole]
    holesFrom t      = (, ctx) <$> splitArrows t
    buildHoles :: Maybe Type -> [NFHole]
    buildHoles b     = Hole <$> (init $ holesFrom $ mkArrow b $ TVar "")
    apps :: (Var, (Maybe Type, Type)) -> NFHole
    apps (x, (b, a)) = HoleApp (x, mkArrow b a) (buildHoles b)

expand (Hole ((TArr a b), ctx)) = [HoleAbstr newVar hole]
  where newVar = ("x", a) -- TODO fresh name
        hole   = Hole (b, newVar : ctx)

expand (HoleAbstr abstr hole) = HoleAbstr abstr <$> expand hole

expand (HoleApp head' holes) = HoleApp head' <$> (sequence $ map expand holes)


run :: NFHole -> [[NFHole]]
run hole = takeWhile (not . null) $ (iterate . concatMap) expand [hole]

runWithTypeAndCtx :: Type -> Context -> [[NFHole]]
runWithTypeAndCtx type' ctx = run $ Hole (type', ctx)

runWithType = flip runWithTypeAndCtx []


-- data TNFHole = TailHole [Decl] Decl [TNFHole] | -- [] x L(B₁; Г) ··· L(Bn; Г)
--                HeadHole [Decl] Hole [TNFHole]   -- λx:A. L(B; Г) []
--                deriving (Show, Eq)
--
-- expand :: TNFHole -> TNFHole
-- expand (HeadHole abstr (type', ctx) tails)
--   | (TVar a)   <- type' =
--      map (\(x, b, _) -> TailHole [] (x, a) ...) (ctxSubArrows ctx a)
--   | (TApp l r) <-
-- -- Too dumb



--
-- -- Abstractor, the head variable and Bem's tails
-- data TNF = TNF [Decl] Decl [TNF]
--
-- instance Show TNF where
--   show (TNF abstr (hvar, _) tails) =
--       concatMap lambda abstr ++ hvar ++ concatMap apply tails
--     where
--       lambda :: Decl -> String
--       lambda (var', type') = "λ" ++ var' ++ ":" ++ show type' ++ ". "
--
--       apply :: TNF -> String
--       apply t@(TNF [] _ _) = " "  ++ show t
--       apply t              = " (" ++ show t ++ ")"
--
--
-- e = TNF [ ("x", TArr (TVar "a") (TVar "b")) ]
--         ("x", TArr (TVar "a") (TVar "b"))
--         [
--           TNF [ ("x", TArr (TVar "a") (TVar "b")) ]
--               ("x", TArr (TVar "a") (TVar "b"))
--               []
--         ]
