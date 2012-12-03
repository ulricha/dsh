module Optimizer.VL.Properties.AbstractDomains where

import           Data.List
import qualified Data.Set as S
import           Data.Tuple
import           Text.PrettyPrint
  
import           Database.Algebra.Dag.Common

-- Type of domain Identifiers
newtype DomainID = ID (AlgNode, String) deriving Eq

instance Show DomainID where
  show (ID (n, c)) = (show n) ++ "." ++ c

type Disjoint = Maybe Domain
              
-- | Abstract active domains of columns.
data Domain = SubDom DomainID Disjoint Domain
            | SubUnionDom DomainID Domain Domain
            | UniverseDom
            | NumberDom Domain
              deriving Show
                       
domainNode :: Domain -> Maybe AlgNode
domainNode (SubDom (ID (n, _)) _ _)      = Just n
domainNode (SubUnionDom (ID (n, _)) _ _) = Just n
domainNode (NumberDom d)                 = domainNode d
domainNode UniverseDom                   = Nothing
              
-- Domains are compared for equality and ordering based on their identifiers
instance Eq Domain where
  UniverseDom          == UniverseDom            = True
  UniverseDom          == _                      = False
  _                    == UniverseDom            = False
  (NumberDom d1)       == (NumberDom d2)         = d1 == d2
  (NumberDom _)        == _                      = False
  _                    == NumberDom _            = False
  (SubDom i1 _ _)      == (SubDom i2 _ _)        = i1 == i2
  (SubDom i1 _ _)      == (SubUnionDom i2 _ _)   = i1 == i2
  (SubUnionDom i1 _ _) == (SubUnionDom i2 _ _)   = i1 == i2
  (SubUnionDom i1 _ _) == (SubDom i2 _ _)        = i1 == i2
  
instance Ord DomainID where
  (ID (n1, c1)) <= (ID (n2, c2)) = n1 <= n2 && c1 <= c2
  
instance Ord Domain where
  _                    <= UniverseDom            = True
  UniverseDom          <= _                      = False
  _                    <= (NumberDom _)          = True
  (NumberDom _)        <= _                      = False
  (SubDom i1 _ _)      <= (SubDom i2 _ _)        = i1 <= i2
  (SubDom i1 _ _)      <= (SubUnionDom i2 _ _)   = i1 <= i2
  (SubUnionDom i1 _ _) <= (SubUnionDom i2 _ _)   = i1 <= i2
  (SubUnionDom i1 _ _) <= (SubDom i2 _ _)        = i1 <= i2
  
domainID :: Show a => AlgNode -> a -> DomainID
domainID n c = ID (n, show c)
                        
-- | True iff d1 occurs in the ancestor history of d2
isSuperDomain :: Domain -> Domain -> Bool
isSuperDomain dom1 dom2@(SubDom _ _ superDom) = dom1 == dom2 || isSuperDomain dom1 superDom
isSuperDomain dom1 dom2@(SubUnionDom _ superDom1 superDom2) = dom1 == dom2
                                                             || isSuperDomain dom1 superDom1
                                                             || isSuperDomain dom1 superDom2
isSuperDomain _ UniverseDom   = False
isSuperDomain _ (NumberDom _) = False
                              
-- | disjoint d returns all domains which are disjoint to d or disjoint to an ancestor of d.
disjointDomains :: Domain -> S.Set Domain
disjointDomains (SubDom _ (Just disjointDomainsDom) superDom) = S.insert disjointDomainsDom $ disjointDomains superDom
disjointDomains (SubDom _ Nothing superDom) = disjointDomains superDom
disjointDomains (SubUnionDom _ superDom1 superDom2) = S.union (disjointDomains superDom1) (disjointDomains superDom2)
disjointDomains UniverseDom = S.empty
disjointDomains (NumberDom _) = S.empty
                    
-- | subDomain d1 d2 is True iff d1 is a subdomain of d2
subDomain :: Domain -> Domain -> Bool
subDomain dom1 dom2 = isSuperDomain dom2 dom1
                      
-- | d1 -||- d2 is True iff d1 and d2 are disjoint. Two domains are disjoint
-- if they are not equal and neither of them has an ancestor to which an ancestor of the
-- other domain is disjoint.
(-||-) :: Domain -> Domain -> Bool
(-||-) dom1 dom2 =
  dom1 /= dom2
  && (not $ S.null $ S.intersection (disjointDomains dom1) (superDomains dom2))
      || (not $ S.null $ S.intersection (superDomains dom1) (disjointDomains dom2))
  
-- | ancestors d returns all domains of which d is a subdomain.
superDomains :: Domain -> S.Set Domain
superDomains dom@(SubDom _ _ superDom) = S.insert dom $ superDomains superDom
superDomains dom@(SubUnionDom _ superDom1 superDom2) = S.insert dom $ S.union (superDomains superDom1)
                                                                              (superDomains superDom2)
superDomains UniverseDom = S.singleton UniverseDom
superDomains (NumberDom n) = S.singleton (NumberDom n)
                       
-- FIXME leastCommonSuperDomain and helper functions are highly inefficient

-- FIXME function has quadratic complexity
minUnion :: [(Domain, Int)] -> [(Domain, Int)] -> [(Domain, Int)]
minUnion ((d, i) : ds1) ds2 = 
  case lookup d ds2 of 
    Just j | j < i -> (d, j) : minUnion ds1 (filter (\(d', _) -> d == d') ds2)
    Just _ -> (d, i) : minUnion ds1 (filter (\(d', _) -> d == d') ds1)
    Nothing -> (d, i) : minUnion ds1 ds2
minUnion [] ds2 = ds2
  
-- Record the distance to all superdomains
superDomainsDist :: Domain -> [(Domain, Int)]
superDomainsDist dom = aux 0 dom
  where aux i superDom@(SubDom _ _ superSuperDom) = 
          (superDom, i) : (aux (i + 1) superSuperDom)
        aux i superDom@(SubUnionDom _ superSuperDom1 superSuperDom2) = 
          (superDom, i) : superDoms 
          where superDoms = minUnion (aux (i + 1) superSuperDom1) (aux (i + 1) superSuperDom2)
        aux i UniverseDom =
          [(UniverseDom, i)]
        aux i (NumberDom n) =
          [(NumberDom n, i)]
        
minIntersect :: [(Domain, Int)] -> [(Domain, Int)] -> [(Domain, Int)]
minIntersect ds1 ds2 = map lookupMin $ (map fst ds1) `intersect` (map fst ds2)
  where lookupMin d =
          case (lookup d ds1, lookup d ds2) of
            (Just m1, Just m2) -> (d, min m1 m2)
            _ -> error "minIntersect: distance value missing"

leastCommonSuperDomain :: Domain -> Domain -> Domain
leastCommonSuperDomain dom1 dom2 = 
  -- trivial case: identity
  if dom1 == dom2
  then dom1
       -- trivial cases: inclusion
  else if subDomain dom1 dom2
       then dom2
       else if subDomain dom2 dom1
            then dom1
                 -- compute all ancestors of the domains together with their distance to the domain
            else case minIntersect (superDomainsDist dom1) (superDomainsDist dom2) of
              [] ->  error "leastCommonSuperDomain: no common superDomain (not even U)"
              superDomainDistances ->  
                -- Take the common superDomain with the minimum distance
                -- Reasoning: All domains should have a common superDomain (at least the domain universe U).
                -- If there is more than one common superDomain, there must be a domain union from which both
                -- domains originate (or U). This domain union (or U) is the common superDomain that is closest to
                -- both domains. 
                let minDist = minimum $ map snd superDomainDistances in 
                 case lookup minDist $ map swap superDomainDistances of
                  Just dom -> dom
                  Nothing -> error "leastCommonSuperDomain: minDist must be in ds"
              
-- Helpers for the construction of domains.
  
-- | Create a new domain that is a subdomain of a given domain.
makeSubDomain :: Show c => AlgNode -> c -> Domain -> Domain
makeSubDomain n c d = SubDom (domainID n c) Nothing d
              
-- | Create a new domain that is a subdomain of a given domain and disjoint
-- to another domain
makeDisjointSubDomain :: Show c => AlgNode -> c -> Domain -> Domain -> Domain
makeDisjointSubDomain n c dd d = SubDom (domainID n c) (Just dd) d
               
-- | Create a new domain that is a subdomain of the union of two domains.
makeUnionSubDomain :: Show c => AlgNode -> c -> Domain -> Domain -> Domain
makeUnionSubDomain n c d1 d2 = 
  if d1 == d2 
  then makeSubDomain n c d1
  else SubUnionDom (domainID n c) d1 d2
  
numberedFrom :: Domain -> Domain -> Bool
numberedFrom (NumberDom d1) d2 = d1 == d2
numberedFrom _              _  = False
                      
-- | Rendering function for a single domain.
renderDomain :: Domain -> Doc
renderDomain d =
  case d of
    SubDom i Nothing superDom -> (text $ show i) <+> text "<-" <+> ident superDom
    SubDom i (Just disjointDom) superDom -> (text $ show i) <+> text "<-" <+> ident superDom <+> text "||" <+> ident disjointDom
    SubUnionDom i superDom1 superDom2 -> (text $ show i) <+> text "<- u" <> parens (ident superDom1 <> comma <+> ident superDom2)
    NumberDom dom -> text $ domID (NumberDom dom)
    UniverseDom -> text "U"
  
    where domID (SubDom i _ _)      = show i
          domID (SubUnionDom i _ _) = show i
          domID (UniverseDom)       = "U"
          domID (NumberDom dom)     = "#(" ++ (domID dom) ++ ")"
  
          ident = text . domID
