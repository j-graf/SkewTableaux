
doc ///
Node
  Key
    Tableaux
  Headline
    a package for computing with Young tableaux
  Description
    Text
      This package provides the classes SkewTableau and YngTableau.
///

doc ///
Key
    SkewTableau
    (net, SkewTableau)
Headline
    a type of HashTable representing a skew Young tableau
Description
  Text
    An object of type SkewTableau is a hash table containing two shapes of type @TO2{Partition,"Partition"}@,
    and a list of box entries. The entries may have any type, except for @TO2{null,"null"}@ objects.

    The inner and outer shapes, $\lambda$ and $\mu$ respectively, can be any sequence of integers. In particular,
    it accepts negative parts, compositions, rows where $\lambda_i < \mu_i$, and compositions where
    $\ell(\lambda)\neq\ell(\mu)$. 
  Example
    lam = new Partition from {4,3,2}
    mu = new Partition from {3,1}
    entryList = {1,2,3,3,9}
    T = skewTableau(lam,mu,entryList)
SeeAlso
    YngTableau
///

doc ///
Key
    YngTableau
Headline
    a type of HashTable representing a (nonskew) Young tableau
Description
  Text
    This is a subclass of @TO2{SkewTableau,"SkewTableau"}@. Each object of YngTableau is essentially just a skew tableau with inner
    shape $\mu=0$.
  Example
    lam = new Partition from {4,3,2}
    entryList = toList(1..(sum toList lam))
    T = yngTableau(lam,entryList)
SeeAlso
    SkewTableau
///

doc ///
Key
    skewTableau
   (skewTableau, Partition, Partition, List)
   (skewTableau, Sequence, List)
   (skewTableau, Partition, List)
   (skewTableau, Partition, Partition)
   (skewTableau, Partition)
   (skewTableau, YngTableau)
Headline
    constructor for type SkewTableau
Usage
    skewTableau(lam, mu, entryList)
    skewTableau((lam,mu),entryList)
Inputs
    lam:Partition
      the outer shape.
    mu:Partition
      the inner shape. If not given, then it is assumed to be the $0$ partition.
    entryList:List
      the filling of the boxes. If not given, then box entries are assumed to be the empty string "".
Outputs
    T:SkewTableau
      a skew Young tableau of shape lam/mu with the given filling
Consequences
    Item
      The list of entries has length equal to $\sum_{i=1}^{\ell(\lambda)}|\lambda_i-\mu_i|$. E.g.,
      if $\lambda=(2)$ and $\mu=(5)$, then the entry list must have length $3$.
Description
  Example
    lam = new Partition from {4,3,2}
    mu = new Partition from {3,1}
    entryList = {1,2,3,3,9}
    T = skewTableau(lam,mu,entryList)
  Text
    We may construct tableaux with any compositions.
  Example
    skewTableau(new Partition from {3,5,1}, new Partition from {0,1}, {7,"&",4,2,"g","u",6,0})
  Text
    The shapes may have negative parts. In this case, a vertical line is drawn by @TO2{(net, SkewTableau),"net"}@
    to indicate that negative parts are to the left.
  Example
    skewTableau(new Partition from {3,-3,-1}, new Partition from {-2,-4,-1})
  Text
    If any $\lambda_i<\mu_i$, then the boxes in that row are drawn shaded.
  Example
    skewTableau(new Partition from {-2,-4,2}, new Partition from {1,-1,-1}, {1,2,3,4,5,6,7,8,9})
  Text
    We may cast an object of type @TO2{YngTableau,"YngTableau"}@ to type SkewTableau.
  Example
    T' = yngTableau(new Partition from {3,1,1})
    skewTableau T'
SeeAlso
  SkewTableau
  YngTableau
  yngTableau
///

doc ///
Key
    yngTableau
   (yngTableau, Partition, List)
   (yngTableau, Partition)
Headline
    constructor for type YngTableau
Usage
    yngTableau(lam, entryList)
Inputs
    lam:Partition
      the shape.
    entryList:List
      the filling of the boxes. If not given, then box entries are assumed to be the empty string "".
Outputs
    T:YngTableau
      a (nonskew) Young tableau of shape lam with the given filling
Consequences
    Item
      The list of entries has length equal to $\sum_{i=1}^{\ell(\lambda)}|\lambda_i|$. E.g.,
      if $\lambda=(-2)$, then the entry list must have length $2$.
Description
  Example
    lam = new Partition from {4,3,2}
    entryList = {1,2,3,4,5,6,7,8,9}
    T = yngTableau(lam,entryList)
  Text
    We may construct tableaux with any compositions.
  Example
    yngTableau(new Partition from {3,5,1}, {7,"&",4,2,"g","u",6,0,-1})
  Text
    The shape may have negative parts. In this case, a vertical line is drawn by @TO2{(net, SkewTableau),"net"}@
    to indicate that negative parts are to the left. If any $\lambda_i<0$, then the boxes in that row are drawn shaded.
  Example
    yngTableau(new Partition from {-2,-4,2})
  Text
    We may cast an object of type YngTableau to type @TO2{SkewTableau,"SkewTableau"}@.
  Example
    T' = yngTableau(new Partition from {3,1,1})
    skewTableau T'
SeeAlso
  SkewTableau
  YngTableau
  skewTableau
///

doc ///
Key
    youngDiagram
   (youngDiagram, Partition, Partition)
   (youngDiagram, Partition)
   (youngDiagram, SkewTableau)
Headline
    a net of the Young diagram
Usage
    youngDiagram(lam, mu)
    youngDiagram T
Inputs
    lam:Partition
      the outer shape.
    mu:Partition
      the inner shape. If not given, if is assumed to be the $0$ partition.
    T:SkewTableau
      a skew tableau.
Outputs
    n:Net
      a net representation of the Young diagram of the given shape
Description
  Example
    T = skewTableau(new Partition from {4,3,1}, new Partition from {2,1}, {1,2,3,4,5})
    youngDiagram T
SeeAlso
  skewTableau
  yngTableau
  ferrersDiagram
///

doc ///
Key
    ferrersDiagram
   (ferrersDiagram, Partition, Partition)
   (ferrersDiagram, Partition)
   (ferrersDiagram, SkewTableau)
Headline
    a net of the Ferrers diagram
Usage
    ferrersDiagram(lam, mu)
    youngDiagramferrersDiagram T
Inputs
    lam:Partition
      the outer shape.
    mu:Partition
      the inner shape. If not given, if is assumed to be the $0$ partition.
    T:SkewTableau
      a skew tableau.
Outputs
    n:Net
      a net representation of the Ferrers diagram of the given shape
Description
  Example
    T = skewTableau(new Partition from {4,3,1}, new Partition from {2,1}, {1,2,3,4,5})
    ferrersDiagram T
SeeAlso
  skewTableau
  yngTableau
  youngDiagram
///

doc ///
Key
   (tex, SkewTableau)
Headline
    LaTeX output for a skew tableau
Usage
    tex T
Inputs
    T:SkewTableau
      a skew tableau.
Outputs
    s:String
      a string with LaTeX code for reproducting the given skew tableau
Description
  Text
    The LaTeX code uses commands from the LaTeX package @HREF("https://github.com/AndrewMathas/aTableau","aTableau")@.
  Example
    T = skewTableau(new Partition from {4,3,1}, new Partition from {2,1}, {1,2,3,4,5})
    tex T
SeeAlso
  skewTableau
  yngTableau
  youngDiagram
  ferrersDiagram
///
