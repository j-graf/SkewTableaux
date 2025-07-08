# SkewTableaux
Macaulay2 package (work-in-progress) for dealing with skew tableaux.

# Examples

## Skew tableau basics

- Create a skew tableau of shape $\lambda/\mu$, where $\lambda=(3,2,2)$, $\mu=(2)$, and with the given filling:
```
lam = new Partition from {4,3,2}
mu = new Partition from {3,1}
entryList = {1,2,3,3,9}
T = skewTableau(lam,mu,entryList)
```

- Check equality (same set difference $\lambda/\mu$ and filling) and strict equality (same shape and filling):
```
lam2 = new Partition from {5,4,3}
mu2 = new Partition from {4,2,1}
entryList2 = {1,2,3,3,9}
T2 = skewTableau(lam2,mu2,entryList2)
T == T2
T === T2
```

- Get the shape (sequence $(\lambda,\mu)$) of a tableau, the 'reduced shape' (set difference), or 'shape0' ($0$'s appended to $\mu$ so that $\lambda$ and $\mu$ have the same length):
```
shape T
reducedShape T2
shape0 T
```

- Get the $i$ th row, $j$ th column, or box $(i,j)$:
```
i = 1
j = 2
T^i
T_j
T_(i,j)
```

- Get the $i$ th row or $j$ th column, with null entries removed:
```
rowEntries(i,T)
colEntries(j,T)
```

- Get the filling, number of rows, number of columns, and number of boxes:
```
entries T
numrows T
numcols T
size T
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

## Algorithms

- Get a (bagged) list of all SSYT of a given shape, and given maximum box entry (default $\ell(\lambda) $):
```
Bag allSSYT(lam,mu,#lam+1)
Bag allSSYT(lam,mu,#lam)
```
