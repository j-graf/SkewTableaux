# Tableaux
Macaulay2 package for constructing (skew) Young tableaux.

# TODO

- Optimization
  - Caching common functions
  - Implement algorithms in C++ via `ForeignFunctions`
- Feature match `SpechtModule`
  - Class `MutableYoungTableau`
  - Algorithms
    - `allStandardTableaux`
    - `numStandardTableaux`
    - `allTabloids`
  - Statistics
    - `columnStabilizer`
    - `firstRowDescent`
    - `readingWord`
    - `rowStabilizer`
- More features
  - Subclass `Tabloid`
  - Remove subclass `YoungTableau`, and rename `SkewTableau` to `YoungTableau`
    - Export method `isSkew`
    - Export methods `outerShape` and `innerShape`
    - Export method `shape` as alias for `outerShape`, raise error if `isSkew`
  - More Booleans
    - `isSemistandard`
    - `isStandard`
    - `isRowStrict` and `isColumnStrict`
    - 

# Examples

## Skew tableau basics

- Create a skew tableau of shape $\lambda/\mu$, where $\lambda=(4,3,2)$, $\mu=(3,1)$, and with the given filling:
```
lam = new Partition from {4,3,2}
mu = new Partition from {3,1}
entryList = {1,2,3,3,9}
T = skewTableau(lam,mu,entryList)
```

- If the filling is ommitted, empty strings are used for each box instead. If a second partition is ommitted, then the $0$ partition is used as the inner shape:
```
skewTableau(lam,mu)
skewTableau(lam)
```

- Get the net of the Young diagram of a given shape, or the net of the tableau itself. The inner shape can also be drawn by calling `drawInnerShape true`:
```
youngDiagram T
youngDiagram(lam,mu)
net T
drawInnerShape true
net T
drawInnerShape false
net T
```

- Get the net of the Ferrers diagram of a given shape:
```
ferrersDiagram T
```

- Create a skew tableau using compositions, negative parts, and negative row lengths:
```
lam' = new Partition from {1,5,0,-1}
mu' = new Partition from {-2,2,0,2}
entryList' = toList(1..(sum for i from 0 to #lam'-1 list abs(lam'#i-mu'#i)))
T' = skewTableau(lam',mu',entryList')
```

- Get the skew shape (sequence $(\lambda,\mu)$ ) of a tableau, or 'padded skew shape' ($0$'s appended so that $\lambda$ and $\mu$ have the same length). Supports multiple assignment:
```
skewShape T'
skewShapePadded T
(lam'',mu'') = skewShapePadded T
```

- Get the $i$ th row, $j$ th column, or box $(i,j)$. Note that row T^i and column T_j will have null entries in positions without boxes, so that when T has only nonnegative parts, we have (T^i)\_j == T\_(i,j):
```
T^1
T_2
T_(1,2)
```

- Get the $i$ th row or $j$ th column, with null entries removed:
```
rowEntries(1,T)
colEntries(2,T)
```

- Get the filling, number of rows, number of columns, and number of boxes:
```
entries T
numrows T
numcols T
size T
```

- Rows are indexed by 0..(#lam-1), and columns are indexed over colRange T:
```
for i from 0 to #lam'-1 do print (T'^i)
print colRange T'
for j in colRange T do print (T'_j)
```

## Useful Methods

- Get LaTeX code for a given tableau, using the LaTeX package [aTableau](https://github.com/AndrewMathas/aTableau):
```
tex T
tex T'
```

- Conjugate a tableau:
```
conjugate T
```

- Check if a tableau is skew, i.e., if $\mu\neq 0$ :
```
isSkew T
```

- Get the position $(i,j)$ of a box, given its index in entryList:
```
indexToPosition(3,T)
```

- Get the index of a box in entryList, given its position $(i,j)$ :
```
positionToIndex((2,0),T)
```

- Iterate over the box entries, or over the box positions:
```
for theBox in entries T do print theBox
for theIndex from 0 to size T - 1 do print indexToPosition(theIndex,T)
```

- Get a list of a tableau's connected components:
```
theComponents = components T
components T'
```

- Concatenate two tableaux, or all of the tableaux in a list:
```
T || T'
verticalConcatenate theComponents
```

- Take the direct sum of two tableaux, or all of the tableaux in a list:
```
T ++ T'
theComponents#0 ++ theComponents#1
```

- Check if a tableau's shape has weakly decreasing, nonnegative parts:
```
isYoungTableau T
isYoungTableau T'
```

- Check if the inner shape is the $0$ partition:
```
isSkew T
```

- Shift a tableau, or unshift a tableau:
```
shift T
shift(T,5)
unshift shift T == T
```

## Algorithms

- Get a (bagged) list of all SSYT of a given shape, and given maximum box entry (default $\ell(\lambda) $):
```
allSSYT(lam,mu,#lam+1)
allSSYT(lam,mu)
```

- Get a (bagged) list of a tableaux with weakly increasing rows of a given shape, and given maximum box entry (default $\ell(\lambda) $):
```
allRowWeakTableaux(lam,mu)
```

- Get a list of all tableau shapes arising from the Jacobi-Trudi identity:
```
allJacobiTrudiShapes(lam,mu)
allJacobiTrudiShapes(lam',mu')
```

- Get a (bagged) list of all tableax arising from the Jacobi-Trudi identity:
```
allJacobiTrudiTableaux(lam,mu)
allJacobiTrudiTableaux(lam',mu')
```
