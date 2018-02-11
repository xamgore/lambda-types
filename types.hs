{-# LANGUAGE TupleSections #-}

import Data.List (find, inits)
import Data.Maybe (mapMaybe, fromMaybe)
import Control.Monad (join, forM)
import Control.Monad.State
import Data.IORef


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
data TNF = TNF Abstr Decl [TNF]

instance Show TNF where
  show (TNF abstr (hvar, htype) tails) =
      concatMap lambda abstr ++ head ++ concatMap apply tails
    where
      head = hvar -- "(" ++ hvar ++ ":" ++ show htype ++ ")"

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

varNameByRank :: Type -> String
varNameByRank = get . fromInteger . rank
  where get idx = if idx < length names then names !! idx else "ℱ"
        names   = ["x", "f", "F", "Ф"]


inc :: State Integer Integer
inc = state (liftM2 (,) (1 +) (1 +))

buildTails :: [Type] -> State Integer [TNF]
buildTails bs =
  forM bs $ \b -> do
    idx <- toLower . show <$> inc
    return $ TNF [] ('M' : idx, b) []  -- TODO M may be in context Г



-- apply two-level grammar's rule as in Wajsberg/Ben-Yelles algorithm
applyRule :: Context -> Type -> Abstr -> [State Integer TNF]

-- L(a) = x L(M1:b1)..L(Mn:bn), (b1 → ... bn → a) in Г
applyRule ctx a@(TVar _) abstr = do
  let funcsToA = ctx `ctxSubArrowTo` a :: [(Var, (Type, [Type]))]

  flip map funcsToA $ \(f, (type', bs)) -> do
    tails <- buildTails bs
    return $ TNF abstr (f, type') tails

-- L(a → b) = \x:a. L(M:b)
applyRule ctx (TArr a b) abstr = pure $ do
  idx <- toLower . show <$> inc
  let m = 'M'              : idx
  let x = varNameByRank a ++ idx
  return $ TNF (abstr ++ [(x, a)]) (m, b) []



-- apply rules for the inner substructure
-- if there are several branches, the result is a cross product
expand :: Context -> TNF -> [State Integer TNF]
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
        zeroGen  = (TNF [] ("M", type') [], 0)



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
