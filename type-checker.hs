-- Code from chapter 9 - A Type Checker

-- The main thing is working through the code to make it more comprehensible my using
-- modern things like maps, monads, type-aliases and sensible var names (gamma?, pls).

import qualified Data.Map as Map

get = (Map.!) -- rename symbol

type VarName = String

data Exp = Var VarName
            | Lambda VarName Exp
            | Apply Exp Exp
            | Let [VarName] [Exp] Exp
            | LetRec [VarName] [Exp] Exp
            deriving (Show, Eq)

type TypeName = [Int]

data TypeExp = TypeVar TypeName
            | TypeCons String [TypeExp]
            deriving (Show, Eq)

-- Built in types.

arrow t1 t2 = TypeCons "arrow" [t1, t2]
int = TypeCons "int" []
cross t1 t2 = TypeCons "cross" [t1, t2]
list t = TypeCons "list" [t]

varsIn :: TypeExp -> [TypeName]
varsIn t = varsIn' t []
            where varsIn' (TypeVar x)     vars = x:vars
                  varsIn' (TypeCons _ ts) vars = foldr varsIn' vars ts

type Subtitution = TypeName -> TypeExp

subType :: Subtitution -> TypeExp -> TypeExp
subType phi (TypeVar name) = phi name
subType phi (TypeCons con ts) = TypeCons con (map (subType phi) ts)

-- Using maybes - no error messages for you!
type Unification = Maybe Subtitution

scomp :: Subtitution -> Subtitution -> Subtitution
scomp phi psi name = subType phi (psi name)

idSubst :: Subtitution
idSubst name = TypeVar name

deltaSubst :: TypeName -> TypeExp -> Subtitution
deltaSubst name t asName
    | name == asName = t
    | otherwise      = TypeVar asName

extend :: Subtitution -> TypeName -> TypeExp -> Unification
extend phi name t
    | t == TypeVar name    = Just phi
    | elem name (varsIn t) = Nothing
    | otherwise            = Just $ (deltaSubst name t) `scomp` phi

type Equation = (TypeExp, TypeExp)

unify :: Subtitution -> Equation -> Unification
unify phi ((TypeVar name), t2)
    | phiret == TypeVar name = extend phi name subt
    | otherwise              = unify phi (phiret, subt)
    where phiret = phi name
          subt   = subType phi t2

unify phi ((TypeCons conname ts), (TypeVar varname)) = unify phi ((TypeVar varname), (TypeCons conname ts))

unify phi ((TypeCons conA tsA), (TypeCons conB tsB))
    | conA == conB = unifyl phi (tsA `zip` tsB)
    | otherwise    = Nothing

unifyl :: Subtitution -> [Equation] -> Unification
unifyl phi eqns = foldr unify' (Just phi) eqns
    where unify' eqn (Just p) = unify p eqn
          unify' eqn Nothing  = Nothing

-- A type scheme lists the schematic (generic) type variable names associated with a type
data Scheme = Scheme [TypeName] TypeExp
                deriving (Show, Eq)

unknowns :: Scheme -> [TypeName]
unknowns (Scheme schematics t) = nonSchematic $ varsIn t
    where nonSchematic = filter (`notElem` schematics)

subScheme :: Subtitution -> Scheme -> Scheme
subScheme phi (Scheme schematics t) = Scheme schematics (subType exclude t)
    where exclude name = if name `elem` schematics then (TypeVar name) else (phi name)

-- Type environments (where we look up the type schemes)

type Env = Map.Map VarName Scheme

unknownsInEnv :: Env -> [TypeName]
unknownsInEnv env = concatMap unknowns (Map.elems env)

subEnv :: Subtitution -> Env -> Env
subEnv phi = Map.map (subScheme phi)

-- Name supplies - lazy sequences of unique identifiers

nextName :: NameSupply -> TypeName
deplete :: NameSupply -> NameSupply
split :: NameSupply -> (NameSupply, NameSupply)

type NameSupply = TypeName
nextName = id
deplete (n:ns) = (n+2:ns)
split ns = (0:ns,1:ns)

-- Infinite list of ids
nameSequence :: NameSupply -> [TypeName]
nameSequence ns = nextName ns : nameSequence (deplete ns)

-- The type checker

type TypeCheckResult = Maybe (Subtitution, TypeExp)

typeCheck :: Env -> NameSupply -> Exp -> TypeCheckResult

typeCheck env ns (Var x) = tcVar env ns x
typeCheck env ns (Apply e1 e2) = tcApp env ns e1 e2
typeCheck env ns (Lambda vs e) = tcLamda env ns vs e
typeCheck env ns (Let xs es e) = tcLet env ns xs es e
typeCheck env ns (LetRec xs es e) = tcLetRec env ns xs es e

-- Helper to check all types in a list.
checkAll :: Env -> NameSupply -> [Exp] -> Maybe (Subtitution, [TypeExp])
checkAll env ns [] = Just (idSubst, [])
checkAll env ns (e:es) = do
    let (ns0, ns1) = split ns
    (phi, t) <- typeCheck env ns0 e -- Check the first expression
    (psi, ts) <- checkAll (subEnv phi env) ns1 es -- Check the rest of the types
    return (combineTypeCheckResults phi t psi ts) -- Combine with all the rest

-- Combine a single type check result with a list of type check results.
-- The involves combining the substitutions and joining the lists (subtyped)
combineTypeCheckResults :: Subtitution -> TypeExp -> Subtitution -> [TypeExp] -> (Subtitution, [TypeExp])
combineTypeCheckResults phi t psi ts = ((psi `scomp` phi), (subType psi t) : ts)

-- Check variables
tcVar :: Env -> NameSupply -> VarName -> TypeCheckResult
tcVar env ns x = do
    scheme <- Map.lookup x env
    return (idSubst, newInstance ns scheme)

newInstance :: NameSupply -> Scheme -> TypeExp
newInstance ns (Scheme vars t) = subType phi t
    where m = Map.fromList $ vars `zip` (nameSequence ns)
          phi = mappingSubst m

-- Subtitution that retrieves var from map if present.
mappingSubst :: Map.Map TypeName TypeName -> Subtitution
mappingSubst al tvn
    | Map.member tvn al = TypeVar (al `get` tvn) -- One of the schematic vars, get new var
    | otherwise         = TypeVar tvn            -- free var, leave unchanged

-- Check applications
tcApp :: Env -> NameSupply -> Exp -> Exp -> TypeCheckResult
tcApp env ns e1 e2 = do
    let tvn = nextName ns
    let ns' = deplete ns
    (phi, [t1, t2]) <- checkAll env ns' [e1, e2] -- Check types of expressions
    psi <- unify phi (t1, t2 `arrow` (TypeVar tvn)) -- Solve with new constraint
    return (psi, psi tvn)

-- check lambda abstractions

tcLamda :: Env -> NameSupply -> VarName -> Exp -> TypeCheckResult
tcLamda env ns x e = do
    let tvn = nextName ns
    let ns' = deplete ns
    let env' = Map.insert x (Scheme [] (TypeVar tvn)) env
    (phi, t) <- typeCheck env' ns' e -- Check the expression
    return (phi, arrow (phi tvn) t)

-- Check let expressions

-- type check the defs, update the env to include these bindings, check
-- the rhs, and then combine the results.
tcLet :: Env -> NameSupply -> [VarName] -> [Exp] -> Exp -> TypeCheckResult
tcLet env ns vars vals e = do
    let (ns0, ns1) = split ns
    let (ns2, ns3) = split ns1
    (phi, ts) <- checkAll env ns0  vals
    let env' = withBindings (subEnv phi env) ns2 vars ts
    (psi, t) <- typeCheck env' ns3 e
    return (psi `scomp` phi, t)

withBindings :: Env -> NameSupply -> [VarName] -> [TypeExp] -> Env
withBindings env ns names types =
    Map.union newTypes env
    where newTypes = Map.fromList (names `zip` schemes)
          schemes = map (createScheme varFilter ns) types
          varFilter = filter $ not . (`elem` unknowns)
          unknowns = unknownsInEnv env

createScheme :: ([TypeName] -> [TypeName]) -> NameSupply -> TypeExp -> Scheme
createScheme filt ns t = Scheme (map snd bindings) t'
    where bindings = zip schematics (nameSequence ns)
          schematics = filt $ uniq (varsIn t)
          t' = subType (mappingSubst (Map.fromList bindings)) t

uniq :: Eq a => [a] -> [a]
uniq xs = f [] xs
    where f acc [] = acc
          f acc (x:xs)
            | x `elem` acc = f acc xs
            | otherwise    = f (x:acc) xs

tcLetRec = error "Not implemented"

-- skk should be the same as id
skk :: Exp
skk = Let ["s", "k"] [s_def, k_def] body
    where var_s = Var "s"
          var_k = Var "k"
          var_x = Var "x"
          var_y = Var "x"
          var_z = Var "z"
          body = Apply (Apply var_s var_k) var_k
          s_def = curried ["x", "y", "z"] body_s
          k_def = curried ["x", "y"] body_k
          body_s = Apply (Apply var_x var_z) (Apply var_y var_z)
          body_k = var_x
          curried vars e = foldr Lambda e vars

main = do
    print skk

