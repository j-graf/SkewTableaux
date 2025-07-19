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
- Create a Young diagram by leaving the filling empty:
```
skewTableau(lam,mu)
```

- Create a skew tableau using compositions, negative parts, and negative row lengths:
```
lam1 = new Partition from {2,7,3,0,-1,0,2,2,-4}
mu1 = new Partition from {-3,5,0,-1,-4,0,1,-1,-2}
entryList1 = toList(1..(sum for i from 0 to #lam1-1 list max(lam1#i-mu1#i,mu1#i-lam1#i)))
T1 = skewTableau(lam1,mu1,entryList1)
```

- Get the shape (sequence $(\lambda,\mu)$ ) of a tableau, the 'reduced shape' (partitions realigned so that the smallest part of $\mu$ is $0$), or 'shape0' ($0$'s appended so that $\lambda$ and $\mu$ have the same length):
```
shape T1
shapeReduced T1
shape0 T
```

- Get the $i$ th row, $j$ th column, or box $(i,j)$:
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

- Get a list of a tableau's connected components:
```
components T
```

## Algorithms

- Get a (bagged) list of all SSYT of a given shape, and given maximum box entry (default $\ell(\lambda) $):
```
allSSYT(lam,mu,#lam+1)
allSSYT(lam,mu,#lam)
```
