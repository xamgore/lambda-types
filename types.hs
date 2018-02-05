import Data.List (find)
import Data.Maybe (mapMaybe)


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

-- subarrows ((a→b)→c) = [(Nothing, (a→b)→c), (Just (a→b), c)]
subArrows :: Type -> [Arr]
subArrows type' = zip left right
  where
    s     = splitArrows type'
    right = scanr1 TArr s
    left  = Nothing : (Just <$> scanl1 TArr s)


subArrowTo :: Type -> Type -> Maybe Arr
subArrowTo t type' = find ((t ==) . snd) (subArrows type')

-- --
-- subArrows :: Type -> [(Type, Type)]
-- subArrows (TVar _)   = []
-- subArrows (TArr l r) = (l, r) : map add (subArrows r)
--   where add (lsub, rsub) = (TArr l lsub, rsub)
--
--
-- first :: (a -> b) -> (a, c) -> (b, c)
-- first f (x, y) = (f x, y)
--
--
-- type TArrow = (Maybe Type, Type)
--
-- -- subArrowTo (c→d) ((a→b)→c→d) = Just (Just a→b, c→d)
-- -- subArrowTo (c)   (c)         = Just (Nothing, c)
-- -- subArrowTo (c)   (a→d)       = Nothing
-- subArrowTo :: Type -> Type -> Maybe TArrow
-- subArrowTo t type'
--   | t == type' = Just (Nothing, t)
--   | otherwise  = first Just <$> arrow
--     where arrow = find ((t ==) . snd) (subArrows type')
--
--
--
-- type Var = String
--
-- -- x:a→b  <=>   ("x", TArr (TVar "a") (TVar "b"))
-- type Decl = (Var, Type)
--
-- -- Г = { x:a, y:a→b }
-- type Context = [Decl]
--
--
-- ctxSubArrows :: Context -> Type -> [(Var, TArrow)]
-- ctxSubArrows ctx t = mapMaybe (traverse (subArrowTo t)) ctx
--
--
-- -- testGetArrowsToType =
-- --     all ((res ==) . ctxSubArrows ctx) [b, atob]
-- --   where
-- b    = TVar "b"
-- atob = TArr (TVar "a") b
-- ctx  = [ ("x", TVar "c"), ("x", atob), ("x", TArr b atob) ]
-- res  = drop 1 ctx

--
-- type Hole = (Type, Context)
--
-- data TNFHole =
--   Hole |                    -- L(B; Г)
--   HoleAbstr Decl TNFHole |  -- λx:A. L(B; Г,x:A)
--   HoleApp   Decl [Hole]     -- x. L(B₁; Г) ··· L(Bn; Г)
--
--
-- expand :: TNFHole -> TNFHole
-- expand = undefined
--
--
--
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
