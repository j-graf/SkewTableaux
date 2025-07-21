newPackage(
    "Tableaux",
    Version => "0.4",
    Date => "July 19, 2025",
    Authors => {
	{Name => "John Graf", Email => "jrgraf@alumni.ncsu.edu", HomePage => "https://j-graf.github.io/"}},
    Headline => "a package for constructing skew tableaux",
    Keywords => {"Combinatorics"},
    AuxiliaryFiles => true,
    DebuggingMode => false,
    PackageImports => {"Permutations"}--,
    --Configuration => {"Convention" => "English", "TexPackage" => "aTableau"}
    )

export {"SkewTableau", "skewTableau",
        "youngDiagram", "ferrersDiagram", "drawInnerShape",
        "skewShape", "skewShapePadded", "rowEntries", "colEntries", "colRange", "applyEntries", "applyPositions",
        "isSkew", "isWeaklyDecreasingShape", "isNonnegativeShape",
        "indexToPosition", "positionToIndex", "positionList",
        "verticalConcatenate", "shift", "unshift", "boxContent", "hookLength",
        "standardize"
        }

export {"YngTableau", "yngTableau",
        "shape"}

export {"allSemistandardTableaux", "allRowWeakTableaux", "allJacobiTrudiDiagrams", "allJacobiTrudiTableaux",
        "numSemistandardTableaux"}


    
-- Implimentation of class SkewTableau

load "Tableaux/SkewTableaux.m2"



-- Implimentation of subclass YngTableau

load "Tableaux/YngTableaux.m2"



-- TODO: Implimentation of subclass Tabloid

-- load "Tableaux/Tabloids.m2"



-- Algorithms involving tableaux

load "Tableaux/algorithms.m2"



-- TODO: Documentation

beginDocumentation()

load "Tableaux/documentation.m2"

end--



-- TODO: Tests

-- load "Tableaux/tests.m2"
