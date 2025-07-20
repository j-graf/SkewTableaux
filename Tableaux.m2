newPackage(
    "Tableaux",
    Version => "0.4",
    Date => "July 19, 2025",
    Authors => {
	{Name => "John Graf", Email => "grafjohnr@gmail.com", HomePage => "https://j-graf.github.io/"}},
    Headline => "a package for constructing skew tableaux",
    Keywords => {"Combinatorics"},
    AuxiliaryFiles => true,
    DebuggingMode => false,
    PackageImports => {"Permutations"}--,
    --Configuration => {"Convention" => "English", "TexPackage" => "aTableau"}
    )

export {"SkewTableau", "skewTableau", "youngDiagram", "ferrersDiagram",
        "skewShape", "skewShapePadded", "rowEntries", "colEntries", "colRange", "isSkew", "isYoungTableau",
        "indexToPosition", "positionToIndex", "verticalConcatenate", "shift", "unshift", "drawInnerShape"}

export {"YngTableau", "yngTableau",
        "shape"}

export {"allSSYT", "allRowWeakTableaux", "allJacobiTrudiShapes", "allJacobiTrudiTableaux"}


    
-- Implimentation of class SkewTableau

load "Tableaux/SkewTableaux.m2"



-- Implimentation of subclass YngTableau

load "Tableaux/YngTableaux.m2"



-- TODO: Implimentation of subclass Tabloid

-- load "Tableaux/Tabloids.m2"



-- Algorithms involving tableaux

load "Tableaux/algorithms.m2"



-- TODO: Documentation

-- load "Tableaux/documentation.m2"



-- TODO: Tests

-- load "Tableaux/tests.m2"
