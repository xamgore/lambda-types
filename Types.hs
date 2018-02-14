{-# LANGUAGE TupleSections #-}

module Types where


import Data.List (find, inits)
import Data.Maybe (mapMaybe, fromMaybe)
import Control.Monad (join, forM)
import Control.Monad.State
import Data.IORef


-- Inductive definition: T = V | T → T
data Type = TVar String | TArr Type Type deriving (Eq, Ord)

instance Show Type where
  show (TVar x) = x
  show (TArr l@(TArr _ _) r) = "(" ++ show l ++ ")→" ++ show r
  show (TArr l            r) =        show l ++  "→" ++ show r


-- Symbol = shows where there is a TVar
-- Example: "a" =>~ ("b" =>= "c") ~>= "d"
--  a→(b→c)→d
infixr 2 ~>, ~>~, ~>=, =>~, =>=
(~>)  = TArr
(~>~) = TArr
l ~>= r = l ~> (TVar r)
l =>~ r = (TVar l) ~> r
l =>= r = (TVar l) ~>= r



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

-- depth of a binary tree with (→) in nodes
depth :: Type -> Integer
depth (TVar _)   = 1
depth (TArr l r) = 1 + max (depth l) (depth r)

rank :: Type -> Integer
rank (TVar _)   = 0
rank (TArr l r) = max (1 + rank l) (rank r)

order :: Type -> Integer
order = (+1) . rank



-- split (a→(b→c)→d) = [a, b→c, d]
split :: Type -> [Type]
split t@(TVar _) = [t]
split (TArr l r) = l : split r

-- By type B1→…→Bn return a list of ([B1,…,Bk], [Bk+1→…→Bn])
subArrows :: Type -> [([Type], Type)]
subArrows type' = zip (init $ inits s) (scanr1 TArr s)
  where s  = split type'

-- subArrowTo d (a→b)→c→d = Just ((a→b)→c→d, [a→b,c])
subArrowTo :: Type -> Type -> Maybe (Type, [Type])
subArrowTo t type' = (type', ) <$> fst <$> find ((t ==) . snd) (subArrows type')


type Var = String

type Decl = (Var, Type) -- y:a→b

type Context = [Decl]   -- Г = { x:a, y:a→b }

type Abstr = [Decl]

has :: Context -> Var -> Bool
ctx `has` v = elem v $ fst <$> ctx

notIn :: Var -> Context -> Bool
v `notIn` ctx = not $ ctx `has` v

-- Find all functions to type t
ctxSubArrowTo :: Context -> Type -> [(Var, (Type, [Type]))]
ctxSubArrowTo ctx t = mapMaybe (traverse (subArrowTo t)) ctx



-- Abstractor, the head variable and Bem's tails
data TNF = TNF Abstr Decl [TNF] deriving (Eq, Ord)

instance Show TNF where
  show (TNF abstr (hvar, htype) tails) =
      concatMap lambda abstr ++ lbrace ++ head ++ concatMap apply tails ++ rbrace
    where
      head = hvar -- "(" ++ hvar ++ ":" ++ show htype ++ ")"

      -- TODO refactor
      brace = case htype of (TVar _)  -> False; otherwise -> True
      lbrace = if brace then "(" else ""
      rbrace = if brace then ")" else ""

      lambda :: Decl -> String
      lambda (var', type') = "λ" ++ var' ++ ":" ++ show type' ++ ". "

      apply :: TNF -> String
      apply t@(TNF [] _ _) = " "  ++ show t
      apply t              = " (" ++ show t ++ ")"



toLower :: String -> String
toLower = map sub where
  sub ch = if '0' <= ch && ch <= '9'
           then toEnum $ fromEnum ch - fromEnum '0' + fromEnum '₀'
           else ch


varNames = ["x", "f", "F", "Ф", "ℱ"]

getElem :: [a] -> Integer -> a
[]     `getElem` _ = error "Empty list"
[x]    `getElem` _ = x
(x:_)  `getElem` 0 = x
(_:xs) `getElem` i = xs `getElem` (i - 1)

setElem :: [a] -> Integer -> (a -> a) -> [a]
setElem []     _ _  = error "Empty list"
setElem [x]    _ op = [op x]
setElem (x:xs) 0 op = (op x : xs)
setElem (x:xs) i op = x : setElem xs (i - 1) op


varNameByRank :: Type -> String
varNameByRank = get . fromInteger . rank
  where get idx = if idx < length varNames
                  then varNames !! idx
                  else last varNames


-- Counter for (M, [x, f, F, Ф, ℱ])
type Counter a = State (Integer, [Integer]) a

incM :: Counter Integer
incM = state (\(m, cs) -> (m, (m + 1, cs)))

inc :: Integer -> Counter (Integer, Integer)
inc idx = state (\(m, cs) ->
  ((m, cs `getElem` idx), (m + 1, setElem cs idx (+1))))


buildTails :: [Type] -> Counter [TNF]
buildTails bs =
  forM bs $ \b -> do
    idx <- toLower . show <$> incM
    return $ TNF [] ('M' : idx, b) []  -- TODO M may be in context Г



-- apply two-level grammar's rule as in Wajsberg/Ben-Yelles algorithm
applyRule :: Context -> Type -> Abstr -> [Counter TNF]

-- L(a) = x L(M1:b1)..L(Mn:bn), (b1 → ... bn → a) in Г
applyRule ctx a@(TVar _) abstr = do
  let funcsToA = ctx `ctxSubArrowTo` a :: [(Var, (Type, [Type]))]

  flip map funcsToA $ \(f, (type', bs)) -> do
    tails <- buildTails bs
    return $ TNF abstr (f, type') tails

-- L(a → b) = \x:a. L(M:b)
applyRule ctx (TArr a b) abstr = pure $ do
  (idm, idx) <- inc (rank a)
  let m = 'M' :              lower idm
  let x = varNameByRank a ++ lower idx
  return $ TNF (abstr ++ [(x, a)]) (m, b) []
  where lower i = if i == 1 then "" else toLower $ show i


-- apply rules for the inner substructure
-- if there are several branches, the result is a cross product
expand :: Context -> TNF -> [Counter TNF]
expand ctx tnf@(TNF abstr (var, type') [])
  | var `notIn` ctx' = applyRule ctx' type' abstr
  | otherwise        = []
  where ctx' = ctx ++ abstr

expand ctx (TNF abstr head' tails) = fmap attachTo . sequence <$> expandedTails
  where expandedTails  = sequence $ map (expand (ctx ++ abstr)) tails
        attachTo tails = TNF abstr head' tails


-- run Wajsberg/Ben-Yelles algorithm and save intermediate results
run :: Context -> Type -> [[TNF]]
run ctx type' = map (fst <$>) $ takeWhile (not . null) $ generate step [zeroGen]
  where generate = iterate . concatMap
        step (tnf, count) = (flip runState count) <$> (expand ctx tnf)
        zeroGen   = (TNF [] ("M", type') [], zeroState)
        zeroState = (1, varNames >> [1])  -- all indexes = 1



hasFreeVarsInCtx :: Context -> TNF -> Bool
hasFreeVarsInCtx ctx (TNF abstr (var, _) tails) =
  var `notIn` ctx' || any (hasFreeVarsInCtx ctx') tails
  where ctx' = ctx ++ abstr


termsOfType :: Type -> [TNF]
termsOfType = filter (not . hasFreeVarsInCtx []) . concat . run []


prettyPrint :: [[TNF]] -> IO ()
prettyPrint history = do
  i <- newIORef 0
  forM_ history $ \terms -> do
    putStr "Generation #"
    readIORef i >>= print
    modifyIORef i (+1)

    forM_ terms $ \term -> do
      print term
    putStrLn ""
