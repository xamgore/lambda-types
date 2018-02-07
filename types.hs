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

type Abstr = [Decl]

notIn :: Var -> Context -> Bool
v `notIn` ctx = not $ elem v $ fst <$> ctx

ctxSubArrowTo :: Context -> Type -> [(Var, Arr)]
ctxSubArrowTo ctx t = mapMaybe (traverse (subArrowTo t)) ctx



-- Abstractor, the head variable and Bem's tails
data TNF = TNF Abstr Decl [TNF]

instance Show TNF where
  show (TNF abstr (hvar, htype) tails) =
      concatMap lambda abstr ++ head ++ concatMap apply tails
    where
      head = "(" ++ hvar ++ ":" ++ show htype ++ ")"

      lambda :: Decl -> String
      lambda (var', type') = "λ" ++ var' ++ ":" ++ show type' ++ ". "

      apply :: TNF -> String
      apply t@(TNF [] _ _) = " "  ++ show t
      apply t              = " (" ++ show t ++ ")"


toTNF :: Var -> Type -> TNF
toTNF v t = TNF [] (v, t) []


e = TNF [ ("x", TArr (TVar "a") (TVar "b")) ]
        ("x", TArr (TVar "a") (TVar "b"))
        [
          TNF [ ("x", TArr (TVar "a") (TVar "b")) ]
              ("x", TArr (TVar "a") (TVar "b"))
              []
        ]


applyRule :: Context -> Type -> Abstr -> [TNF]
applyRule ctx (TArr a b) abstr = [TNF (abstr ++ [("x", a)]) ("M", b) []]
applyRule ctx a@(TVar _) abstr = map apps $ ctxSubArrowTo ctx a
  where
    buildHoles :: Maybe Type -> [TNF]
    buildHoles b     = zipWith toTNF ((("M" ++) . show) <$> [1..]) (init $ splitArrows $ mkArrow b $ TVar "")
    apps :: (Var, Arr) -> TNF
    apps (x, (b, a)) = TNF abstr (x, mkArrow b a) (buildHoles b)


expand :: Context -> TNF -> [TNF]
expand ctx tnf@(TNF abstr (var, type') [])
  | var `notIn` ctx' = applyRule ctx' type' abstr
  | otherwise        = [] -- TODO or [tnf]?
  where ctx' = ctx ++ abstr

expand ctx (TNF abstr head' tails) = TNF abstr head' <$> expandedTails
  where expandedTails = sequence $ map (expand (ctx ++ abstr)) tails




run :: Context -> Type -> [[TNF]]
run ctx type' = takeWhile (not . null) $ generate (expand ctx) [zeroGen]
  where generate = iterate . concatMap
        zeroGen  = TNF [] ("M", type') []
